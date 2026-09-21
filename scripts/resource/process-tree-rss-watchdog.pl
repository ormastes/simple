#!/usr/bin/perl
# Host protection only. The ordinary compile acceptance target remains <1 GiB.
# ps reports KiB on macOS and Linux. Keep one supervisor alive at 100 ms;
# do not fork a shell/awk/sleep pipeline for every sample.
use strict;
use warnings;
use POSIX qw(setsid WNOHANG);
use Time::HiRes qw(time sleep alarm);

my %opt = ( 'max-rss-kib' => 5859375, 'interval-ms' => 100,
            'timeout-seconds' => 0, 'term-grace-seconds' => 1 );
while (@ARGV && $ARGV[0] ne '--') {
    my $arg = shift @ARGV;
    $arg =~ /^--(max-rss-kib|interval-ms|timeout-seconds|term-grace-seconds|receipt)=(.+)$/
        or die "rss-guard: invalid option\n";
    $opt{$1} = $2;
}
@ARGV > 1 && shift(@ARGV) eq '--' or die "rss-guard: missing command\n";
for my $key (qw(max-rss-kib interval-ms timeout-seconds term-grace-seconds)) {
    $opt{$key} =~ /^\d+$/ or die "rss-guard: invalid $key\n";
}
$opt{'max-rss-kib'} > 0 && $opt{'max-rss-kib'} <= 6291456
    or die "rss-guard: cap must be between 1 and 6291456 KiB\n";
$opt{'interval-ms'} > 0 && $opt{'interval-ms'} <= 100
    or die "rss-guard: sample interval must be between 1 and 100 ms\n";
my $leader = 0;
my %known;
my %groups;
my ($peak, $samples, $child_status, $interrupted);
$peak = $samples = $interrupted = 0;
my $started = time;
my $last = {};
my $ps_pid = 0;
my ($previous_sample, $sample_gap_max_ms) = (0, 0);

sub snapshot {
    local $ENV{LC_ALL} = 'C';
    # List form bypasses shell pipelines, so a failing ps cannot be hidden by awk.
    $ps_pid = open(my $ps, '-|', 'ps', '-axo', 'pid=,ppid=,pgid=,rss=,stat=,lstart=');
    defined($ps_pid) or die "cannot start ps";
    my %all;
    local $SIG{ALRM} = sub { kill 'KILL', $ps_pid; die "ps timed out" };
    alarm($opt{'interval-ms'} / 1000);
    while (my $line = <$ps>) {
        $line =~ /^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\S+)\s+(.+?)\s*$/
            or die "malformed ps row";
        my ($pid, $parent, $group, $rss, $state, $identity) = ($1,$2,$3,$4,$5,$6);
        $all{$pid} = { parent => 0+$parent, group => 0+$group, rss => 0+$rss,
                     zombie => scalar($state =~ /^Z/), identity => $identity };
    }
    close($ps) or die "ps failed";
    alarm 0;
    %all or die "empty ps output";
    ++$samples;
    return \%all;
}

sub members {
    my ($all) = @_;
    for my $group (keys %groups) {
        delete $groups{$group} if exists($all->{$group}) &&
            $all->{$group}{identity} ne $groups{$group};
    }
    my %selected;
    for my $pid (keys %$all) {
        $selected{$pid} = 1 if $pid == $leader || $all->{$pid}{group} == $leader ||
            $groups{$all->{$pid}{group}} ||
            (exists($known{$pid}) && $known{$pid} eq $all->{$pid}{identity});
    }
    my $changed = 1;
    while ($changed) {
        $changed = 0;
        for my $pid (keys %$all) {
            if (!$selected{$pid} && $selected{$all->{$pid}{parent}}) {
                $selected{$pid} = 1; $changed = 1;
            }
        }
    }
    delete $selected{$$};
    for my $pid (keys %selected) {
        $known{$pid} = $all->{$pid}{identity};
        # Retain observed session/group leaders as well as PIDs. A member may
        # fork between measurement and STOP; its child's group survives reparent.
        $groups{$pid} = $all->{$pid}{identity} if $all->{$pid}{group} == $pid;
    }
    return grep { !$all->{$_}{zombie} } keys %selected;
}

sub reap {
    return if defined $child_status;
    my $got = waitpid($leader, WNOHANG);
    $child_status = $? if $got == $leader;
}

sub quiesce {
    # Freeze before terminating: TERM handlers can otherwise fork new survivors.
    # Rediscover after STOP until three empty samples establish quiescence.
    my $empty = 0;
    for (1..100) {
        kill 'STOP', -$leader;
        kill 'STOP', -$_ for keys %groups;
        my $all = eval { snapshot() };
        if (!$all) {
            alarm 0;
            kill 'KILL', $ps_pid if $ps_pid > 0;
            # Kill the anchored group even if sampling is broken. Cached PIDs
            # alone are unsafe to signal after reuse; escaped identities cannot
            # be validated here, so report containment unverified and fail closed.
            kill 'KILL', -$leader;
            kill 'KILL', -$_ for keys %groups;
            reap();
            return 0;
        }
        my @live = members($all);
        kill 'STOP', @live if @live;
        kill 'KILL', -$leader;
        kill 'KILL', -$_ for keys %groups;
        kill 'KILL', @live if @live;
        reap();
        $empty = @live ? 0 : $empty + 1;
        return 1 if $empty >= 3;
        sleep 0.02;
    }
    return 0;
}

sub receipt {
    my ($status, $code, $quiet) = @_;
    my $body = "status=$status\nexit_status=$code\nroot_pid=$leader\n" .
        "max_rss_kib=$opt{'max-rss-kib'}\npeak_rss_kib=$peak\nsamples=$samples\n" .
        "interval_ms=$opt{'interval-ms'}\nsample_gap_max_ms=$sample_gap_max_ms\n" .
        "containment_scope=observed-descendants-and-process-groups\n" .
        "hard_memory_limit=0\nquiescent=$quiet\n";
    print STDERR $body if $code == 88 || $code == 89;
    if (defined $opt{receipt}) {
        my $tmp = "$opt{receipt}.tmp.$$";
        open(my $fh, '>', $tmp) or die "rss-guard: cannot write receipt\n";
        print $fh $body;
        close($fh) && rename($tmp, $opt{receipt}) or die "rss-guard: cannot publish receipt\n";
    }
}

pipe(my $gate_read, my $gate_write) or die "rss-guard: pipe failed\n";
$leader = fork();
defined($leader) or die "rss-guard: fork failed\n";
if ($leader == 0) {
    close $gate_write;
    defined(setsid()) && getpgrp() == $$ or POSIX::_exit(89);
    my $go;
    sysread($gate_read, $go, 1) == 1 && $go eq 'G' or POSIX::_exit(89);
    close $gate_read;
    exec { $ARGV[0] } @ARGV or POSIX::_exit(127);
}
close $gate_read;
$SIG{TERM} = sub { $interrupted = 143 };
$SIG{INT} = sub { $interrupted = 130 };
$SIG{HUP} = sub { $interrupted = 129 };
$SIG{PIPE} = 'IGNORE';
my ($status, $code) = ('complete', 0);
my $released = 0;
while (1) {
    my $sample_started = time;
    my $gap = $previous_sample ? ($sample_started - $previous_sample) * 1000 : 0;
    $sample_gap_max_ms = $gap if $gap > $sample_gap_max_ms;
    $previous_sample = $sample_started;
    my $all = eval { snapshot() };
    if (!$all) {
        alarm 0;
        warn "rss-guard: measurement failed: $@\n";
        ($status, $code) = ('rss-measurement-failed', 89); last;
    }
    $last = $all;
    my @live = members($all);
    my $rss = 0; $rss += $all->{$_}{rss} for @live;
    $peak = $rss if $rss > $peak;
    if ($rss >= $opt{'max-rss-kib'}) {
        ($status, $code) = ('rss-cap-exceeded', 88); last;
    }
    if (!$released) {
        # Both successful sampling and confirmed session isolation are required
        # before releasing exec. A child failure cannot launch unguarded work.
        if (exists($all->{$leader}) && $all->{$leader}{group} == $leader) {
            syswrite($gate_write, 'G', 1) == 1 or do {
                ($status, $code) = ('rss-startup-failed', 89); last;
            };
            close $gate_write;
            $released = 1;
        } elsif (time - $started >= 2) {
            ($status, $code) = ('rss-startup-failed', 89); last;
        }
    }
    if ($interrupted) { ($status, $code) = ('interrupted', $interrupted); last }
    if ($opt{'timeout-seconds'} && time - $started >= $opt{'timeout-seconds'}) {
        ($status, $code) = ('timeout', 124); last;
    }
    reap();
    if (defined $child_status) {
        $code = ($child_status & 127) ? 128 + ($child_status & 127) : $child_status >> 8;
        last;
    }
    my $remaining = $opt{'interval-ms'} / 1000 - (time - $sample_started);
    sleep($remaining) if $remaining > 0;
}
close $gate_write unless $released;
if ($code == 124 || $interrupted) {
    # Preserve the timeout wrapper's TERM/grace contract for artifact flushing.
    # RSS breaches use immediate STOP/KILL because allocations must stop.
    kill 'TERM', -$leader;
    kill 'TERM', -$_ for keys %groups;
    my $grace_end = time + $opt{'term-grace-seconds'};
    while (time < $grace_end) {
        my $all = eval { snapshot() };
        if (!$all) { alarm 0; ($status, $code) = ('rss-measurement-failed', 89); last }
        my @live = members($all);
        last unless @live;
        my $rss = 0; $rss += $all->{$_}{rss} for @live;
        $peak = $rss if $rss > $peak;
        if ($rss >= $opt{'max-rss-kib'}) { ($status, $code) = ('rss-cap-exceeded', 88); last }
        sleep 0.02;
    }
}
my $quiet = quiesce();
if (!$quiet && $code != 89) { ($status, $code) = ('rss-containment-unverified', 89) }
receipt($status, $code, $quiet);
exit $code;
