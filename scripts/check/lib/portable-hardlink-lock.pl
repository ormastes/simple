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

sub group_state {
    my ($pgid) = @_;
    return 'unknown' unless defined($pgid) && $pgid =~ /\A[1-9][0-9]*\z/;
    return 'live' if kill(0, -$pgid);
    return 'live' if $! == EPERM;
    return 'dead' if $! == ESRCH;
    return 'unknown';
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
    print group_state($pgid), "\n";
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
