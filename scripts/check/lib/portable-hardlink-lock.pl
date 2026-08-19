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
    open(my $fh, '-|', 'ps', '-o', "$field=", '-p', $pid) or return;
    my @lines = <$fh>;
    close($fh) or return;
    return unless @lines == 1;
    $lines[0] =~ s/^\s+//;
    $lines[0] =~ s/\s+$//;
    return length($lines[0]) ? $lines[0] : undef;
}

sub process_snapshot {
    my ($pid) = @_;
    return unless defined($pid) && $pid =~ /\A[1-9][0-9]*\z/;
    my $start_one = ps_value('lstart', $pid);
    return unless defined($start_one);
    my $pgid = ps_value('pgid', $pid);
    return unless defined($pgid) && $pgid =~ /\A[1-9][0-9]*\z/;
    my $start_two = ps_value('lstart', $pid);
    return unless defined($start_two) && $start_one eq $start_two;
    return (unpack('H*', $start_one), $pgid);
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
    @ARGV <= 1 or fail_usage();
    my $owner = shift(@ARGV) // getppid();
    $owner =~ /\A[1-9][0-9]*\z/ or exit 1;
    my ($start, $pgid) = process_snapshot($owner);
    defined($start) or exit 1;
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
