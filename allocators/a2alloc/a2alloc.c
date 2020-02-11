#include <sys/types.h>
#include <stdlib.h>
#include <stdio.h>
#include <strings.h>
#include <unistd.h>
#include <pthread.h>
#include <assert.h>

#include "mm_thread.h"
#include "memlib.h"
#include "malloc.h"

typedef ptrdiff_t vaddr_t;

static
void fill_deadbeef(void *vptr, size_t len)
{
	u_int32_t *ptr = vptr;
	size_t i;

	for (i=0; i < len/sizeof(u_int32_t); i++) {
		ptr[i] = 0xdeadbeef;
	}
}

///////////////////////////////////
// Defines (taken from kheap.c)

#define PAGE_SIZE 4096
#if defined(__GNUC__)
#if __LP64__
#define PAGE_FRAME 0xfffffffffffff000
#else
#define PAGE_FRAME 0xfffff000
#endif /* __X86_64__ */
#endif /* __GNUC__ */

#define NSIZES 9

static const size_t sizes[NSIZES] = { 8, 16, 32, 64, 128, 256, 512, 1024, 2048 };

#define SMALLEST_SUBPAGE_SIZE 8
#define LARGEST_SUBPAGE_SIZE 2048

////////////////////////////////////////////////////////////////////
// Structs


struct freelist {
	struct freelist *next;
};

struct big_freelist {
	int npages;
	struct big_freelist *next;
};

struct superblock {
	struct superblock *next;		
	struct freelist *flist;			// LL of free blocks
	vaddr_t pageaddr_and_blocktype;	// The address and block size of the superblock
	int used;						// The number of bytes used in the superblock
	pthread_mutex_t sbLock;
};

struct heap {
	int used;                             
	int allocated;
	pthread_mutex_t heapLock;
	struct superblock *sizebases[NSIZES]; // Superblocks by size class
};

// MACROS FROM kheap.c re purposed for our uses

#define SB_PAGEADDR(sb)  ((sb)->pageaddr_and_blocktype & PAGE_FRAME)
#define SB_BLOCKTYPE(sb) ((sb)->pageaddr_and_blocktype & ~PAGE_FRAME)
#define MKPAB(pa, blk) 	 (((pa)&PAGE_FRAME) | ((blk) & ~PAGE_FRAME))

///////////////////////////////////////////////////////////////////
// Globals


// Global heap at heaps[0]
// Rest from [1..numProcessors]
// (From Hoard paper)
static struct heap *heaps;
static int numProcessors;
static struct superblock *fresh_superblocks;
static struct superblock *recycled_superblocks;
static struct big_freelist *bigblocks;

pthread_mutex_t global_lock = PTHREAD_MUTEX_INITIALIZER;

///////////////////////////////////////////////////////////////////
// Helper Functions


// Small helper function that can be inlined
static
inline
int hashTID(int tid) 
{
	// There are 2*numProcessors local heaps
	// then add one to account for the global heap
	// at index 0

	return (tid % numProcessors) + 1;
}

// Small helper function that can be inlined (taken from kheap.c)
static
inline
int blocktype(size_t sz)
{
	unsigned i;
	for (i = 0; i < NSIZES; i++) {
		if (sz <= sizes[i]) {
			return i;
		}
	}

	printf("Subpage allocator cannot handle allocation of size %lu\n", 
	      (unsigned long)sz);
	exit(1);

	// keep compiler happy
	return 0;
}

static struct superblock *
alloc_superblock(void)
{
	pthread_mutex_lock(&global_lock);

	struct superblock *sb;
	
    if (recycled_superblocks) {
		sb = recycled_superblocks;
		recycled_superblocks = recycled_superblocks->next;
		pthread_mutex_unlock(&global_lock);
		return sb;
	}
	
	if (fresh_superblocks) {
		sb = fresh_superblocks;
		fresh_superblocks = fresh_superblocks->next;
		pthread_mutex_unlock(&global_lock);
		return sb;
	}

	sb = (struct superblock *) mem_sbrk(PAGE_SIZE);
	if (sb) {
		bzero(sb, PAGE_SIZE);
		fresh_superblocks = sb+1;
		struct superblock *tmp = fresh_superblocks;
		int nrefs = PAGE_SIZE / sizeof(struct superblock) - 1;
		int i;
		for (i = 0; i < nrefs-1; i++) {
			tmp->next = tmp+1;
			tmp = tmp->next;
		}
		tmp->next = NULL;
	}
	pthread_mutex_unlock(&global_lock);
	return sb;
}

static void free_superblock(struct superblock *sb)
{
    pthread_mutex_lock(&global_lock);
    
	sb->next = recycled_superblocks;
	recycled_superblocks = sb;
	
	pthread_mutex_unlock(&global_lock);
}

static void *alloc_bigblock(size_t sz)
{
    /* Handle requests bigger than LARGEST_SUBPAGE_SIZE 
	 * We simply round up to the nearest page-sized multiple
	 * after adding some overhead space to hold the number of 
	 * pages. (taken from kheap.c)
	 */
	 
    void *result = NULL;

	sz += SMALLEST_SUBPAGE_SIZE;
	/* Round up to a whole number of pages. */
	int npages = (sz + PAGE_SIZE - 1)/PAGE_SIZE;
    
    pthread_mutex_lock(&global_lock);
    
	/* Check if we happen to have a chunk of the right size already */
	struct big_freelist *tmp = bigblocks;
	struct big_freelist *prev = NULL;
	while (tmp != NULL) {
		if (tmp->npages > npages) {
			/* Carve the block in two pieces */
			tmp->npages -= npages;
			int *hdr_ptr = (int *)((char *)tmp+(tmp->npages*PAGE_SIZE));
			*hdr_ptr = npages;
			result = (void *)((char *)hdr_ptr + SMALLEST_SUBPAGE_SIZE);
			break;
		} else if (tmp->npages == npages) {
			/* Remove block from freelist */
			if (prev) {
				prev->next = tmp->next;
			} else {
				bigblocks = tmp->next;
			}
			int *hdr_ptr = (int *)tmp;
			assert(*hdr_ptr == npages);
			result = (void *)((char *)hdr_ptr + SMALLEST_SUBPAGE_SIZE);
			break;
		} else {
			prev = tmp;
			tmp = tmp->next;
		}
	}

	if (result == NULL) {
		/* Nothing suitable in freelist... grab space with mem_sbrk */
		int *hdr_ptr = (int *)mem_sbrk(npages*PAGE_SIZE);
		if (hdr_ptr != NULL) {
			*hdr_ptr = npages;
			result = (void *)((char *)hdr_ptr + SMALLEST_SUBPAGE_SIZE);
		}
	}
    
    pthread_mutex_unlock(&global_lock);
    return result;
}

static void free_bigblock(void *ptr)
{
    /* (taken from kheap.c) */    
    
	int *hdr_ptr = (int *)((char *)ptr - SMALLEST_SUBPAGE_SIZE);
	
	pthread_mutex_lock(&global_lock);

	struct big_freelist *newfree = (struct big_freelist *) hdr_ptr;
	assert(newfree->npages == *hdr_ptr);
	newfree->next = bigblocks;
	bigblocks = newfree;
	
	pthread_mutex_unlock(&global_lock);
}

////////////////////////////////////////////////////////////////////
// Main Functions


void *mm_malloc(size_t sz)
{
	// if sz > PAGE_SIZE/2, allocate the block from the OS and return
	if (sz > LARGEST_SUBPAGE_SIZE) {
	    return alloc_bigblock(sz);
	}

	void *retptr;

	// heap number <- hash(the current thread)
	int heapNum = hashTID(getTID());
	assert(heapNum > 0);
	unsigned blktype = blocktype(sz);
	assert(blktype >= 0);
	struct heap *threadHeap = heaps + heapNum;
	
	// Lock the heap
	pthread_mutex_lock(&(threadHeap->heapLock));
	
	// Scan heap for superblock of corresponding block size
	// from fullest to least full
	struct superblock *sb;
	for (sb = threadHeap->sizebases[blktype]; sb != NULL; sb = sb->next) {
		assert(SB_BLOCKTYPE(sb) == blktype);
     
		if ((sb->used / sizes[blktype]) < (PAGE_SIZE / sizes[blktype])) {
			break;
		}
	}
	
	// If no superblock with free space
	if (sb == NULL) {
		// Check global heap for a superblock
		struct heap *globalHeap = heaps;
		for (sb = globalHeap->sizebases[blktype]; sb != NULL; sb = sb->next) {
			assert(SB_BLOCKTYPE(sb) == blktype);
			
			if ((sb->used / sizes[blktype]) < (PAGE_SIZE / sizes[blktype])) {
				break;
			}
		}
        
		// If there is none in global heap
		if (sb == NULL) {
			// Allocate PAGE_SIZE bytes for superblock
			sb = alloc_superblock();
			if (sb == NULL) {
				// No more memory
				printf("malloc: Subpage allocator couldn't get a page\n"); 
				return NULL;
			}

			vaddr_t sbpage = SB_PAGEADDR(sb);
			if (sbpage == 0) {
				pthread_mutex_lock(&global_lock);
				sbpage = (vaddr_t)mem_sbrk(PAGE_SIZE);
				pthread_mutex_unlock(&global_lock);
				if (sbpage == 0) {
				    free_superblock(sb);
					printf("malloc: Subpage allocator couldn't get a page\n"); 
					return NULL;
				}
			}
            
            sb->used = 0;
			sb->pageaddr_and_blocktype = MKPAB(sbpage, blktype);
			pthread_mutex_init(&(sb->sbLock), NULL);
			
			// Build freelist
			vaddr_t fla = sbpage;
			struct freelist *fl = (struct freelist *)fla;
			fl->next = NULL;
			int i;
			for (i = 1; i < (PAGE_SIZE / sizes[blktype]); i++) {
				fl = (struct freelist *)(fla + i * sizes[blktype]);
				fl->next = (struct freelist *)(fla + (i - 1) * sizes[blktype]);
				assert(fl != fl->next);
			}
			
			sb->flist = fl;
			sb->next = threadHeap->sizebases[blktype];
			threadHeap->sizebases[blktype] = sb; 	
			threadHeap->allocated += PAGE_SIZE;
		} else {
			// Transfer the superblock sb from global heap
			pthread_mutex_lock(&(globalHeap->heapLock));
			
			globalHeap->used -= sb->used;
			threadHeap->used += sb->used;
			globalHeap->allocated -= PAGE_SIZE;
			threadHeap->allocated += PAGE_SIZE;

			// ***Remove from global heap not fully implemented***
			
		    //if (sb == globalHeap->sizebases[blktype]) {
			//        globalHeap->sizebases[blktype] = sb->next;
            //} else {
			//    struct superblock *tmp;
			//    for (tmp = globalHeap->sizebases[blktype]; tmp != NULL; tmp = tmp->next) {
			//        assert(SB_BLOCKTYPE(tmp) == blktype);
			//        
			//        if (sb == tmp->next) {
			//            tmp->next = sb->next;
			//            break;
			//        }
		    //    }
			//}

			// Unlock global heap
			pthread_mutex_unlock(&(globalHeap->heapLock));

            // Add to this threads heap
			sb->next = threadHeap->sizebases[blktype];
			threadHeap->sizebases[blktype] = sb;
		}
	}
	
	assert(sb != NULL);
	assert(sb->flist != NULL);
    
    // allocate a block from the superblock
	retptr = sb->flist;
	sb->flist = sb->flist->next;
	sb->used += sizes[blktype];
	threadHeap->used += sizes[blktype];
	
	// Unlock heap
	pthread_mutex_unlock(&(threadHeap->heapLock));
	
	// Return a pointer to a block from the superblock 
	return retptr;
}

void mm_free(void *ptr)
{
	if (ptr == NULL) {
	    return;
    } else {
        int blktype;
        int heapNum;
        int i;
        vaddr_t ptrAddr;
        vaddr_t sbPageAddr;
        struct superblock *sb = NULL;
        struct heap *threadHeap;
        
        ptrAddr = (vaddr_t)ptr;
        
        // Find the superblock that contains ptr
        for (heapNum = 0; heapNum < (numProcessors + 1) && sb == NULL; heapNum++) {
            threadHeap = heaps + heapNum;
            for (i = 0; i < NSIZES && sb == NULL; i++) { 
                for (sb = threadHeap->sizebases[i]; sb != NULL; sb = sb->next) {
                    sbPageAddr = SB_PAGEADDR(sb);
                    blktype = SB_BLOCKTYPE(sb);
                    
                    // Check for corruption
                    assert(blktype >= 0 && blktype < NSIZES);
                    
                    if (ptrAddr >= sbPageAddr && ptrAddr < (sbPageAddr + PAGE_SIZE)) {
                        break;
                    }
                }
            }           
        }
        
        // Not a small block allocation
        if (sb == NULL) {
            free_bigblock(ptr);
            return;
        }
        
        // Check for proper block positioning and alignment
        assert((ptrAddr - sbPageAddr) < PAGE_SIZE && 
               (ptrAddr - sbPageAddr) % sizes[blktype] == 0);
        
        // Lock the superblock and heap
        pthread_mutex_lock(&(sb->sbLock));
        pthread_mutex_lock(&(threadHeap->heapLock));
        
        // Clear block to 0xdeadbeef
        fill_deadbeef(ptr, sizes[blktype]);
        
        ((struct freelist *)ptr)->next = sb->flist;
        sb->flist = (struct freelist *)ptr;
        
        sb->used = sb->used - sizes[blktype];
        threadHeap->used = threadHeap->used - sizes[blktype];
        
        // Nothing left to do if global heap
        if (heapNum == 0) {
            // Unlock the superblock and heap
            pthread_mutex_unlock(&(sb->sbLock));
            pthread_mutex_unlock(&(threadHeap->heapLock));
            return;
        }
        
        // Emptiness threshold and number of free superblocks required for
        // transfer to global heap (from Hoard paper)
        float f = 1.0; // (not fully implemented, so never transfers)
        int K = 0;      
        if (threadHeap->used < threadHeap->allocated - (K * PAGE_SIZE) && 
            threadHeap->used < (1 - f) * threadHeap->allocated) {
            struct superblock *sb1 = sb;
            
            // Find emptiest superblock in this heap
            for (i = 0; i < NSIZES; i++) {
                if (threadHeap->sizebases[i] != NULL &&
                    threadHeap->sizebases[i]->used < sb1->used) {
                    sb1 = threadHeap->sizebases[i];
                }
            }
            
            // Transfer emptiest superblock to global heap if its at least f empty
            int sb1Blktype = SB_BLOCKTYPE(sb1);
            if (sb1->used <= (1 - f) * sizes[sb1Blktype]) {
                // Lock global heap
                pthread_mutex_lock(&(heaps->heapLock));
                
                heaps->used = heaps->used + sb1->used;
                threadHeap->used = threadHeap->used - sb1->used;
                heaps->allocated = heaps->allocated + PAGE_SIZE;
                threadHeap->allocated = threadHeap->allocated - PAGE_SIZE;
                
                // ***Add to global heap not fully implemented***
                
                //threadHeap->sizebases[sb1Blktype] = sb1->next;
                //sb1->next = heaps->sizebases[sb1Blktype];
                //heaps->sizebases[sb1Blktype] = sb1;;
                
                // Unlock global heap
                pthread_mutex_unlock(&(heaps->heapLock));        
            } 
        }
        
        // Unlock superblock and heap
        pthread_mutex_unlock(&(sb->sbLock));
        pthread_mutex_unlock(&(threadHeap->heapLock));
        return;
    }
}

int mm_init(void)
{
	if (dseg_lo == NULL && dseg_hi == NULL) {
		// Intialize allocator.
		int status;
		if ((status = mem_init()) != 0) {
			return status;
		}

		// Get page worth of memory to store heap structures. 
		heaps = (struct heap *) mem_sbrk(PAGE_SIZE);
		
		// Set the memory to zero
		bzero(heaps, PAGE_SIZE);

		if (heaps) {
			int i;
			numProcessors = getNumProcessors();
			
			// Check that appropriate amount of memory is gathered for this.
			assert((numProcessors + 1) * sizeof(struct heap) <= PAGE_SIZE);
			
			// Initialize P+1 heaps (Hoard paper).
			struct heap *tmp = heaps;
			for (i = 0; i < numProcessors + 1; i++) {
				pthread_mutex_init(&(tmp->heapLock), NULL);
				tmp++;
			}
		}
	}

	return 0;
}

