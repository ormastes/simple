#!/usr/bin/perl
use strict;
use warnings;
use FindBin;
use File::Temp qw(tempdir);
use File::Copy qw(copy);
use POSIX qw(setpgid);
use Time::HiRes qw(sleep);

if (@ARGV && $ARGV[0] eq '--workload') {
    my $root = $$;
    pipe(my $ready, my $notify) or die $!;
    my $child = fork(); defined $child or die $!;
    if (!$child) {
        close $ready;
        setpgid(0, 0) == 0 or die $!;
        my $group = $$;
        my $grandchild = fork(); defined $grandchild or die $!;
        if (!$grandchild) { sleep 10; exit 0 }
        open my $pids, '>', "$ARGV[1].tmp" or die $!;
        print $pids "$root\n$group\n$grandchild\n";
        close $pids;
        rename "$ARGV[1].tmp", $ARGV[1] or die $!;
        print $notify "ready\n"; close $notify;
        sleep 10; exit 0;
    }
    close $notify;
    <$ready> or die 'child did not start';
    sleep 10; exit 0;
}

if ($^O ne 'darwin') { print "SKIP: Darwin metadata cleanup\n"; exit 0 }
my $tmp = tempdir(CLEANUP => 1);
my $test = $FindBin::Bin;
my $guard = "$test/../../../scripts/resource/process-tree-rss-watchdog.pl";
chomp(my $compiler = `command -v cc`);
local $ENV{RSS_TEST_REAL_CC} = $compiler;
local $ENV{RSS_TEST_OBSERVER_REAL} = "$tmp/observer";
local $ENV{RSS_TEST_OBSERVER_PROXY} = "$test/fixture_process_observer_cleanup_proxy.pl";
local $ENV{RSS_TEST_CLEANUP_PIDS} = "$tmp/work.pids";
local $ENV{CC} = "$test/fixture_process_observer_cc.shs";
my $guard_pid = fork(); defined $guard_pid or die $!;
if (!$guard_pid) {
    open STDOUT, '>', "$tmp/guard.log" or die $!;
    open STDERR, '>&', \*STDOUT or die $!;
    exec $^X, $guard, "--receipt=$tmp/receipt", '--timeout-seconds=4',
        '--', $^X, $0, '--workload', "$tmp/work.pids";
    die "exec: $!";
}
waitpid($guard_pid, 0);
my $status = $? >> 8;
if (my $evidence = $ENV{RSS_TEST_CLEANUP_EVIDENCE_DIR}) {
    -d $evidence or die "missing evidence directory: $evidence";
    for my $item (['guard.log', 'cleanup-guard.log'], ['receipt', 'cleanup-receipt.env'],
                  ['work.pids', 'cleanup-work.pids'], ['work.pids.denied', 'cleanup-denial-marker.txt']) {
        copy("$tmp/$item->[0]", "$evidence/$item->[1]") or die "retain evidence: $!"
            if -e "$tmp/$item->[0]";
    }
}
open my $log, '<', "$tmp/guard.log" or die $!;
my $output = do { local $/; <$log> };
$status == 89 or die "expected failure status89, got$status: $output";
open my $receipt, '<', "$tmp/receipt" or die "missing receipt: $output";
my %receipt = map { chomp; split /=/, $_, 2 } <$receipt>;
for my $entry ([status => 'rss-measurement-failed'], [quiescent => 1],
               [observer_errors => 1], [observer_restarts => 1]) {
    ($receipt{$entry->[0]} // '') eq $entry->[1]
        or die "unexpected $entry->[0]: $output";
}
$output =~ /injected persistent detail EPERM/ or die 'detail denial not exercised';
-e "$tmp/work.pids.denied" or die 'denial before complete workload metadata';
open my $pids, '<', "$tmp/work.pids" or die 'workload did not launch';
my @pids = map { chomp; /^\d+$/ or die 'bad PID'; 0+$_ } <$pids>;
@pids == 3 or die 'missing child/grandchild';
for my $pid (@pids) {
    open my $ps, '-|', 'ps', '-p', $pid, '-o', 'stat=' or die $!;
    my $state = <$ps> // ''; close $ps;
    $state eq '' || $state =~ /^\s*Z/ or die "surviving workload PID $pid: $state";
}
print "PASS: persistent detail denial, metadata-only cleanup, dead root, retained child group and grandchild, exit89/quiescent1\n";
