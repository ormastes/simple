#!/usr/bin/perl
use strict;
use warnings;
my $fault = $ENV{LOCK_OBSERVER_FAULT} // die 'missing fixture fault';
my $state = $ENV{LOCK_OBSERVER_STATE} // die 'missing fixture state';
@ARGV == 2 && $ARGV[0] eq '--identity' or die 'wrong observer request';
if ($fault eq 'malformed') { print "invalid\n"; exit 0 }
if ($fault eq 'oversized') { print 'x' x 257; exit 0 }
if ($fault eq 'failed') { exit 89 }
if ($fault eq 'timeout') {
    open(my $fh, '>', $state) or die $!;
    print {$fh} "$$\n"; close($fh) or die $!;
    sleep 20;
    exit 0;
}
if ($fault eq 'reused') {
    my $birth = -e $state ? '100:2' : '100:1';
    open(my $fh, '>', $state) or die $!;
    close($fh) or die $!;
    print "$birth 0 Tue Sep 22 12:00:00 2026\n";
    exit 0;
}
die 'unknown fixture fault';
