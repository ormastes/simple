#!/usr/bin/perl
use strict;
use warnings;
use IPC::Open2 qw(open2);
use Time::HiRes qw(sleep);
$| = 1;
exit 77 if ($ENV{RSS_TEST_OBSERVER_FAULT} // '') eq 'close';
my ($input, $output);
my $child = open2($input, $output, $ENV{RSS_TEST_OBSERVER_REAL});
$SIG{TERM} = sub { kill 'KILL', $child; exit 89 };
my $samples = 0;
while (my $line = <STDIN>) {
    if ($line eq "M\n") {
        ++$samples;
        # The first request warms admission before there is a workload.
        if ($samples > 1) {
            if (($ENV{RSS_TEST_OBSERVER_FAULT} // '') eq 'oversize') {
                print 'X' x 8192, "\n"; next;
            }
            if (($ENV{RSS_TEST_OBSERVER_FAULT} // '') eq 'malformed') {
                print "M invalid\nE\n"; next;
            }
            exit 77 if -e $ENV{RSS_TEST_PS_FAIL_AFTER};
            sleep($ENV{RSS_TEST_PS_DELAY} // 0);
        }
    }
    print {$output} $line or die 'proxy write';
    while (my $answer = <$input>) {
        print $answer;
        last if $line ne "M\n" || $answer eq "E\n";
    }
}
close $output;
waitpid($child, 0);
