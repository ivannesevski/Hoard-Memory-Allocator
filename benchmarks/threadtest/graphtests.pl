#!/usr/bin/perl

use strict;

my $dir=$ARGV[0];
if (!(-e $dir and -d $dir)) {
    print "USAGE: graphtests.pl <directory containing Results subdirectory>\n";
    exit;
}

my $graphtitle = "threadtest - runtimes";

my @namelist = ("libc", "kheap", "a2alloc");
#my @namelist = ("libc", "kheap");
#my @namelist = ("a2alloc");
my %names;

# This allows you to give each series a name on the graph
# that is different from the file or directory names used
# to collect the data.  We happen to be using the same names.
$names{"libc"} = "libc";
$names{"kheap"} = "kheap";
$names{"a2alloc"} = "a2alloc";

my $name;
my $nthread = 8;

foreach $name (@namelist) {
    open G, "> $dir/Results/$name/data";
    for (my $i = 1; $i <= 8; $i++) {
	open F, "$dir/Results/$name/threadtest-$i";
	my $total = 0;
	my $count = 0;
	my $min = 1e30;
	my $max = -1e30;

	while (<F>) {
	    chop;
	    # Runtime results
	    if (/([0-9]+\.[0-9]+) seconds/) {
		#	 print "$i\t$1\n";
		my $current = $1;
		$total += $1;
		$count++;
		if ($current < $min) {
		    $min = $current;
		}
		if ($current > $max) {
		    $max = $current;
		}
	    }

	}
	if ($count > 0) {
	    #	   print G "$i\t$avg\t$min\t$max\n";
	    print G "$i\t$min\n";
	} else {
	    print "oops count is zero, $name, threadtest-$i\n";
	}

	close F;
    }
    close G;


}


open PLOT, "|gnuplot";
print PLOT "set terminal pdfcairo\n";
print PLOT "set output \"$dir/threadtest.pdf\"\n";
print PLOT "set title \"$graphtitle\"\n";
print PLOT "set ylabel \"Runtime (seconds)\"\n";
print PLOT "set xlabel \"Number of threads\"\n";
print PLOT "set xrange [0:9]\n";
print PLOT "set yrange [0:*]\n";
print PLOT "plot ";

foreach $name (@namelist) {

    my $titlename = $names{$name};
    if ($name eq $namelist[-1]) {
	print PLOT "\"$dir/Results/$name/data\" title \"$titlename\" with linespoints\n";
    } else {
	print PLOT "\"$dir/Results/$name/data\" title \"$titlename\" with linespoints,";
    }
}
close PLOT;


