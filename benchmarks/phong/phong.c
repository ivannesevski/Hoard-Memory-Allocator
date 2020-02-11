/*
 * This is a modified version of the phong memory allocator benchmark
 * included with the Hoard distribution.
 *
 */
#include	<errno.h>
#include	<stdlib.h>
#include	<string.h>
#include	<pthread.h>
#include        <stdio.h>
#include        <unistd.h>

#include "mm_thread.h"
#include "timer.h"
#include "malloc.h"
#include "memlib.h"


#define	N_THREAD	256
#define N_ALLOC		1000000
static int		Nthread = N_THREAD;
static int		Nalloc = N_ALLOC;
static size_t		Minsize = 10;
static size_t		Maxsize = 1024;
static int              numCPU = 0;

int error(char* mesg)
{
	ssize_t rv;
	rv = write(2, mesg, strlen(mesg));
	exit(1);
}

void* allocate(void* arg)
{
	int		k, p, q, c;
	size_t		sz, nalloc, len;
	char		**list;
	size_t		*size;
	int		thread = (int)((long)arg);

	unsigned int	rand = 0; /* use a local RNG so that threads work uniformly */
#define FNV_PRIME	((1<<24) + (1<<8) + 0x93)
#define FNV_OFFSET	2166136261
#define RANDOM()	(rand = rand*FNV_PRIME + FNV_OFFSET)

	setCPU((thread+1)%numCPU);

	nalloc = Nalloc/Nthread; /* do the same amount of work regardless of #threads */

	if(!(list = (char**)mm_malloc(nalloc*sizeof(char*))) )
		error("failed to allocate space for list of objects\n");
	if(!(size = (size_t*)mm_malloc(nalloc*sizeof(size_t))) )
		error("failed to allocate space for list of sizes\n");
	memset(list, 0, nalloc*sizeof(char*));
	memset(size, 0, nalloc*sizeof(size_t));

	for(k = 0; k < nalloc; ++k)
	{
		/* get a random size favoring smaller over larger */
		len = Maxsize-Minsize+1;
		for(;;)
		{	sz = RANDOM() % len; /* pick a random size in [0,len-1] */
			if((RANDOM()%100) >= (100*sz)/len) /* this favors a smaller size */
				break;
			len = sz; /* the gods want a smaller length, try again */
		}
		sz += Minsize;

		if(!(list[k] = mm_malloc(sz)) )
			error("malloc failed\n");
		else
		{	size[k] = sz;
			for(c = 0; c < 10; ++c)
				list[k][c*sz/10] = 'm';
		}

		if(k < 1000)
			continue;

		/* get an interval to check for free and realloc */
		p = RANDOM() % k;
		q = RANDOM() % k;
		
		if(p > q) 
			{ c = p; p = q; q = c; }

		for(; p <= q; ++p)
		{	if(list[p])
			{	if(RANDOM()%2 == 0 ) /* 50% chance of being freed */
				{	mm_free(list[p]);
					list[p] = 0;
					size[p] = 0;
				}
#if 0 /* We are not implementing realloc for the assignment */
				else if(RANDOM()%4 == 0 ) /* survived free, check realloc */
				{	sz = size[p] > Maxsize ? size[p]/4 : 2*size[p];
					if(!(list[p] = realloc(list[p], sz)) )
						error("realloc failed\n");
					else
					{	size[p] = sz;
						for(c = 0; c < 10; ++c)
							list[p][c*sz/10] = 'r';
					}
				}
#endif /* not implementing realloc */
			}
		}
	}

	/* Clean up - free any list items still remaining. */
	for(k = 0; k < nalloc; ++k)
	{
		if (list[k] != 0) {
			mm_free(list[k]);
		}
	}

	mm_free(list);
	mm_free(size);

	return (void*)0;
}

int main(int argc, char* argv[])
{
	int		i, rv;
	void		*status;
	pthread_t	th[N_THREAD];
	pthread_attr_t attr;
	struct timespec start_time, end_time;
	double elapsed;
	
	for(; argc > 1; --argc, ++argv)
	{	if(argv[1][0] != '-')
			continue;
		else if(argv[1][1] == 'a') /* # malloc calls */
			Nalloc = atoi(argv[1]+2);
		else if(argv[1][1] == 't') /* # threads */
			Nthread = atoi(argv[1]+2);
		else if(argv[1][1] == 'z') /* min block size */
			Minsize = atoi(argv[1]+2);
		else if(argv[1][1] == 'Z') /* max block size */
			Maxsize = atoi(argv[1]+2);
	}
		
	if(Nalloc <= 0 || Nalloc > N_ALLOC)
		Nalloc = N_ALLOC;
	if(Nthread <= 0 || Nthread > N_THREAD)
		Nthread = N_THREAD;
	if(Minsize <= 0)
		Minsize = 1;
	if(Maxsize < Minsize)
		Maxsize = Minsize;

	printf ("Running with %d allocations, %d threads, min size = %ld, max size = %ld\n",
		Nalloc, Nthread, Minsize, Maxsize);

	/* Call allocator-specific initialization function */
	mm_init();

	numCPU = getNumProcessors();

	initialize_pthread_attr(PTHREAD_CREATE_JOINABLE, SCHED_RR, -10,
				PTHREAD_EXPLICIT_SCHED, PTHREAD_SCOPE_SYSTEM, &attr);

	/* Get the starting time */
	clock_gettime(CLOCK_MONOTONIC_RAW, &start_time);
	
	for(i = 0; i < Nthread; ++i)
	{	if((rv = pthread_create(&th[i], &attr, allocate, (void*)((long)i))) != 0 )
			error("Failed to create thread\n");
	}

	for(i = 0; i < Nthread; ++i)
	{	if((rv = pthread_join(th[i], &status)) != 0 )
			error("Failed waiting for thread\n");
	}

	/* Get the finish time */
	clock_gettime(CLOCK_MONOTONIC_RAW, &end_time);
	elapsed = timespec_diff(&start_time, &end_time);

	printf ("Time elapsed = %f seconds\n", elapsed);
	printf ("Memory used = %ld bytes\n",mem_usage());

	
	return 0;
}
