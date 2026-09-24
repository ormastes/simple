#!/usr/bin/perl
use strict;
use warnings;
use IPC::Open2 qw(open2);
$| = 1;
my ($input, $output);
my $child = open2($input, $output, $ENV{RSS_TEST_OBSERVER_REAL});
my %metadata_pids;
my $denial_marker = "$ENV{RSS_TEST_CLEANUP_PIDS}.denied";
while (my $line = <STDIN>) {
    if ($line =~ /^R / && -e $ENV{RSS_TEST_CLEANUP_PIDS}) {
        open my $pids, '<', $ENV{RSS_TEST_CLEANUP_PIDS} or die $!;
        my @pids = map { chomp; /^\d+$/ or die 'bad workload PID'; 0+$_ } <$pids>;
        # The whole fixture must already be in the forwarded metadata table;
        # creating its PID file between M and R must not deny too early.
        if (-e $denial_marker || (@pids == 3 && !grep { !$metadata_pids{$_} } @pids)) {
            if (!-e $denial_marker) {
                open my $marker, '>', $denial_marker or die $!;
                print $marker "all workload identities were present in metadata\n";
                close $marker;
                # Root death reproduces the reparented retained child group.
                kill 'KILL', $pids[0];
            }
            # The marker makes denial persist across observer restarts.
            close $output;
            waitpid($child, 0);
            print STDERR "injected persistent detail EPERM; metadata remains available\n";
            exit 89;
        }
    }
    %metadata_pids = () if $line eq "M\n";
    print {$output} $line or die 'proxy write';
    while (my $answer = <$input>) {
        $metadata_pids{$1} = 1 if $line eq "M\n" && $answer =~ /^M (\d+) /;
        print $answer;
        last if $line ne "M\n" || $answer eq "E\n";
    }
}
close $output;
waitpid($child, 0);
