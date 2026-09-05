#!/usr/bin/env perl
use strict;
use warnings;
use Errno qw(EPERM ESRCH);
use Fcntl qw(:mode);

sub fail_usage {
    die "usage: portable-hardlink-lock.pl COMMAND ARGS...\n";
}

sub path_identity {
    my ($path) = @_;
    my @st = lstat($path);
    return unless @st && S_ISREG($st[2]) && !S_ISLNK($st[2]);
    return ($st[0], $st[1]);
}

sub ps_value {
    my ($field, $pid) = @_;
    local $ENV{LC_ALL} = 'C';
    # Fork explicitly so the child's stderr can be silenced: a `ps` without
    # -o support (MSYS / Git Bash `ps` accepts only -aeflsupW) writes a usage
    # error here on every call. The caller treats undef as "unsupported" and
    # falls back to proc_stat_snapshot; the noise would be pure confusion.
    my $child = open(my $fh, '-|');
    return unless defined($child);
    if (!$child) {
        open(STDERR, '>', '/dev/null');
        exec('ps', '-o', "$field=", '-p', $pid);
        exit 127;
    }
    my @lines = <$fh>;
    close($fh) or return;
    return unless @lines == 1;
    $lines[0] =~ s/^\s+//;
    $lines[0] =~ s/\s+$//;
    return length($lines[0]) ? $lines[0] : undef;
}

# Fallback identity source for hosts whose `ps` has no -o (MSYS / Git Bash).
# /proc/<pid>/stat field 22 is starttime and field 5 is pgrp; MSYS provides
# both. starttime is a strictly stronger PID-reuse discriminator than lstart
# (clock ticks since boot, not whole seconds). comm (field 2) may contain
# spaces and parens, so split after the LAST ')'.
sub proc_stat_snapshot {
    my ($pid) = @_;
    open(my $fh, '<', "/proc/$pid/stat") or return;
    my $line = <$fh>;
    close($fh) or return;
    return unless defined($line);
    my $close_paren = rindex($line, ')');
    return if $close_paren < 0;
    my $rest = substr($line, $close_paren + 1);
    $rest =~ s/\A\s+//;
    my @fields = split(/\s+/, $rest);
    # @fields[0] is field 3 (state), so field N is index N - 3.
    return unless @fields >= 20;
    my $pgid = $fields[2];
    my $start = $fields[19];
    return unless defined($start) && $start =~ /\A[0-9]+\z/;
    return unless defined($pgid) && $pgid =~ /\A[0-9]+\z/;
    return ($start, $pgid);
}

sub process_snapshot {
    my ($pid) = @_;
    return unless defined($pid) && $pid =~ /\A[1-9][0-9]*\z/;
    my $start_one = ps_value('lstart', $pid);
    if (defined($start_one)) {
        my $pgid = ps_value('pgid', $pid);
        return unless defined($pgid) && $pgid =~ /\A[1-9][0-9]*\z/;
        my $start_two = ps_value('lstart', $pid);
        return unless defined($start_two) && $start_one eq $start_two;
        return (unpack('H*', $start_one), $pgid);
    }
    my ($proc_start_one, $proc_pgid) = proc_stat_snapshot($pid);
    return unless defined($proc_start_one);
    return unless defined($proc_pgid) && $proc_pgid =~ /\A[1-9][0-9]*\z/;
    # Read twice and compare, exactly as the ps path does, so a PID recycled
    # between the two reads cannot be mistaken for the original process.
    my ($proc_start_two) = proc_stat_snapshot($pid);
    return unless defined($proc_start_two) && $proc_start_one eq $proc_start_two;
    return (unpack('H*', $proc_start_one), $proc_pgid);
}

sub pid_absent {
    my ($pid) = @_;
    return 0 if kill(0, $pid);
    return 0 if $! == EPERM;
    return 1 if $! == ESRCH;
    return 0;
}

sub group_state_detail {
    my ($pgid) = @_;
    return ('unknown', 0) unless defined($pgid) && $pgid =~ /\A[1-9][0-9]*\z/;
    return ('live', 1) if kill(0, -$pgid);
    return ('live', 0) if $! == EPERM;
    return ('dead', 0) if $! == ESRCH;
    return ('unknown', 0);
}

# Full (pid, ppid, pgid, starttime) table from /proc. Returns an empty list
# when /proc scanning is unavailable (e.g. macOS); callers must then keep the
# kill()-based verdict unchanged.
sub proc_table {
    return unless -r "/proc/$$/stat";
    opendir(my $dh, '/proc') or return;
    my @rows;
    for my $entry (readdir($dh)) {
        next unless $entry =~ /\A[1-9][0-9]*\z/;
        open(my $fh, '<', "/proc/$entry/stat") or next;
        my $line = <$fh>;
        close($fh) or next;
        next unless defined($line);
        my $close_paren = rindex($line, ')');
        next if $close_paren < 0;
        my $rest = substr($line, $close_paren + 1);
        $rest =~ s/\A\s+//;
        my @fields = split(/\s+/, $rest);
        next unless @fields >= 20;
        my ($ppid, $pgrp, $start) = ($fields[1], $fields[2], $fields[19]);
        next unless defined($start) && $start =~ /\A[0-9]+\z/;
        next unless defined($pgrp) && $pgrp =~ /\A[0-9]+\z/;
        next unless defined($ppid) && $ppid =~ /\A[0-9]+\z/;
        push(@rows, [$entry + 0, $ppid + 0, $pgrp + 0, $start]);
    }
    closedir($dh);
    return @rows;
}

# The recorded pgid carries no start-time identity of its own, so a bare
# kill(0, -pgid) proves only that SOME process occupies that group-id slot,
# not that the recorded owner's group survives. On Windows/MSYS the OS
# recycles pids aggressively, so an unrelated later session leader (plus its
# descendants) can occupy a dead owner's pgid slot indefinitely -- measured
# 2026-08-31: claim-state printed "live" for a dead owner whose recorded
# pgid slot was held by an unrelated leader, so the stale bootstrap lock was
# never reclaimed and the next run timed out waiting for output ownership.
#
# When the claim was minted under portable-session-exec.pl the owner IS the
# group leader (pid == pgid), so the recorded owner start-time identifies
# the GROUP as well and the verdict can be refined. Refinement runs only
# when ALL of the following hold; otherwise the kill()-based verdict is
# returned byte-identically:
#   - the recorded claim has pid == pgid (the shape our own create path
#     produces via the session wrapper; foreign shapes keep old semantics),
#   - kill(0, -pgid) SUCCEEDED (same-uid group, so /proc shows every
#     member; the EPERM path is never refined -- under hidepid another
#     user's members are invisible and demoting EPERM to dead would be the
#     false-dead two-writers corruption this lock exists to prevent),
#   - a /proc scan is available (Linux, MSYS/Cygwin; macOS opts out).
# It demotes "live" to "dead" in exactly two positively-verified cases:
#   (a) no process holds the pgid AND a re-check of kill(0, -pgid) now
#       reports ESRCH (closes the scan-vs-kill race), or
#   (b) the leader slot is held by a process whose start-time differs from
#       the recorded owner's (an impostor from pid recycling), EVERY other
#       member's parent chain leads into the impostor set, and a re-read of
#       the impostor's start-time is unchanged (a pid recycled between the
#       two reads cannot slip through).
# Any member that cannot be positively attributed to the impostor --
# reparented to pid 1, an unreadable row, a broken or over-long chain --
# keeps the group "live" (fail closed), and the surviving member pids are
# reported on stderr so an operator can act on a genuinely wedged group.
sub refine_leader_group_state {
    my ($pgid, $expected_start_hex) = @_;
    my @rows = proc_table();
    return 'live' unless @rows;
    my %row_by_pid;
    my @members;
    for my $row (@rows) {
        $row_by_pid{$row->[0]} = $row;
    }
    for my $row (@rows) {
        push(@members, $row) if $row->[2] == $pgid;
    }
    if (!@members) {
        return 'dead' if !kill(0, -$pgid) && $! == ESRCH;
        return 'live';
    }
    my $leader = $row_by_pid{$pgid};
    if (!defined($leader) || $leader->[2] != $pgid) {
        print STDERR "portable-lock: owner pid is gone but group $pgid " .
            'members survive (pids ' .
            join(' ', map { $_->[0] } @members) .
            "); lock stays held until they exit or are killed\n";
        return 'live';
    }
    my $leader_start_hex = unpack('H*', $leader->[3]);
    return 'live' if $leader_start_hex eq $expected_start_hex;
    my %impostor = ($pgid => 1);
    for my $member (@members) {
        next if $impostor{$member->[0]};
        my @chain = ($member->[0]);
        my $cursor = $member->[1];
        my $verdict = '';
        for (my $hop = 0; $hop < 64; $hop++) {
            if ($impostor{$cursor}) {
                $verdict = 'impostor';
                last;
            }
            if ($cursor <= 1 || !defined($row_by_pid{$cursor})) {
                $verdict = 'genuine';
                last;
            }
            push(@chain, $cursor);
            $cursor = $row_by_pid{$cursor}->[1];
        }
        if ($verdict eq 'impostor') {
            $impostor{$_} = 1 for @chain;
            next;
        }
        print STDERR "portable-lock: recorded pgid $pgid leader was " .
            "recycled, but member pid $member->[0] cannot be attributed to " .
            "the recycled leader; keeping the lock held (fail closed)\n";
        return 'live';
    }
    my ($leader_start_again) = proc_stat_snapshot($pgid);
    return 'live' unless defined($leader_start_again) &&
        unpack('H*', $leader_start_again) eq $leader_start_hex;
    print STDERR "portable-lock: recorded pgid $pgid was recycled by an " .
        "unrelated process (start-time mismatch); the recorded owner group " .
        "is positively absent, allowing stale-lock reclaim\n";
    return 'dead';
}

sub claim_fields {
    my ($path) = @_;
    open(my $fh, '<', $path) or return;
    my %fields;
    while (my $line = <$fh>) {
        chomp($line);
        return if $line !~ /\A([a-z_]+)=([^\r\n]*)\z/;
        return if exists($fields{$1});
        $fields{$1} = $2;
    }
    close($fh) or return;
    return \%fields;
}

my $command = shift(@ARGV) // fail_usage();

if ($command eq 'link') {
    @ARGV == 2 or fail_usage();
    link($ARGV[0], $ARGV[1]) or exit 1;
    exit 0;
}

if ($command eq 'identity') {
    @ARGV == 1 or fail_usage();
    my @identity = path_identity($ARGV[0]);
    @identity or exit 1;
    print "$identity[0]:$identity[1]\n";
    exit 0;
}

if ($command eq 'owner-snapshot') {
    @ARGV == 0 or fail_usage();
    my $owner = getppid();
    my ($start, $pgid) = process_snapshot($owner);
    defined($start) && getppid() == $owner or exit 1;
    print "pid=$owner\nstart_hex=$start\npgid=$pgid\n";
    exit 0;
}

if ($command eq 'claim-state') {
    @ARGV == 3 or fail_usage();
    my ($pid, $expected_start, $pgid) = @ARGV;
    $pid =~ /\A[1-9][0-9]*\z/ && $expected_start =~ /\A[0-9a-f]+\z/ &&
        $pgid =~ /\A[1-9][0-9]*\z/ or exit 2;
    my ($actual_start) = process_snapshot($pid);
    if (defined($actual_start)) {
        if ($actual_start eq $expected_start) {
            print "live\n";
            exit 0;
        }
    } elsif (!pid_absent($pid)) {
        print "unknown\n";
        exit 0;
    }
    my ($group_verdict, $group_kill_ok) = group_state_detail($pgid);
    if ($group_verdict eq 'live' && $group_kill_ok && "$pid" eq "$pgid") {
        $group_verdict = refine_leader_group_state($pgid, $expected_start);
    }
    print "$group_verdict\n";
    exit 0;
}

if ($command eq 'unlink-if-match') {
    @ARGV == 7 or fail_usage();
    my ($path, $dev, $ino, $nonce, $pid, $start, $pgid) = @ARGV;
    $nonce =~ /\A[0-9a-f]{32}\z/ or exit 1;
    my @before = path_identity($path);
    @before && "$before[0]" eq $dev && "$before[1]" eq $ino or exit 1;
    my $fields = claim_fields($path);
    defined($fields) or exit 1;
    ($fields->{nonce} // '') eq $nonce &&
        ($fields->{owner_pid} // '') eq $pid &&
        ($fields->{owner_start_hex} // '') eq $start &&
        ($fields->{owner_pgid} // '') eq $pgid or exit 1;
    my @after = path_identity($path);
    @after && "$after[0]" eq $dev && "$after[1]" eq $ino or exit 1;
    unlink($path) or exit 1;
    exit 0;
}

fail_usage();
