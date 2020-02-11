#!/usr/local/bin/perl

# Expect 1 argument to be directory path where we are running

use strict;
my $dir=$ARGV[0];
if (!(-e $dir and -d $dir)) {
    print "USAGE: graphtests.pl <directory containing Results subdirectory>\n";
    exit;
}

my $graphtitle = "Larson throughput";

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
    for (my $i = 1; $i <= $nthread; $i++) {
	open F, "$dir/Results/$name/larson-$i";
	my $total = 0;
	my $count = 0;
	my $min = 1e30;
	my $max = -1e30;

	while (<F>) {
	    chop;
	    # Throughput results
	    if (/Throughput =\s+([0-9]+)\s+/) {
		# print G "$i\t$1\n";
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
	    my $avg = $total / $count;
	    print G "$i\t$avg\t$min\t$max\n";
	} else {
	    print "oops count is zero, $name, larson-$i\n";
	}

	close F;
    }
    close G;   

}

open PLOT, "|gnuplot";
print PLOT "set terminal pdfcairo\n";
print PLOT "set output \"$dir/larson.pdf\"\n";
print PLOT "set title \"$graphtitle\"\n";
print PLOT "set ylabel \"Throughput (memory ops per second)\"\n";
print PLOT "set xlabel \"Number of threads\"\n";
print PLOT "set xrange [0:17]\n";
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
