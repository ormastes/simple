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

# --- Darwin start-time identity -------------------------------------------
#
# Darwin has no /proc, and Apple Silicon macOS refuses raw sysctl(2) syscalls:
# measured 2026-09-16 on this host, syscall(202) returns ENOENT for every mib,
# including CTL_KERN/KERN_OSTYPE -- only the fork-safety list (getpid, ...)
# survives, and sysctl(8) does not expose kern.proc.* either. The remaining
# in-box source with sub-second resolution is libproc's proc_pidinfo(3) with
# PROC_PIDTBSDINFO: pbi_start_tvsec/pbi_start_tvusec, the same p_starttime the
# Linux table reads as clock ticks, at microsecond resolution. That is a
# strictly stronger recycled-pid discriminator than ps lstart's whole seconds,
# which the 2026-09-12 bug record measured as unsafe for this refinement.
#
# A tiny python3 ctypes probe reads the fixed fields (measured layout on this
# host, flavor 3, 136 bytes returned: pid@12 ppid@16 start_tvsec@120
# start_tvusec@128; this struct variant carries NO pbi_pgid field -- pgid is
# an exact integer attribute and keeps coming from ps). When python3, the
# libproc call, or the sanity check is unavailable, everything below returns
# undef and the callers keep the pre-port behaviour: ps lstart identities and
# no darwin reclaim refinement. That fallback is deliberate and fail-closed.
my $DARWIN_BSDINFO_PY = q{
import ctypes, sys, time
pid = int(sys.argv[1])
lib = ctypes.CDLL("libSystem.B.dylib")
lib.proc_pidinfo.restype = ctypes.c_int
lib.proc_pidinfo.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_uint64,
                             ctypes.c_void_p, ctypes.c_int]
buf = (ctypes.c_byte * 256)()
n = lib.proc_pidinfo(pid, 3, 0, buf, len(buf))
if n < 136:
    sys.exit(1)
b = bytes(buf)
got = int.from_bytes(b[12:16], "little")
ppid = int.from_bytes(b[16:20], "little")
sec = int.from_bytes(b[120:128], "little")
usec = int.from_bytes(b[128:136], "little")
now = time.time()
if got != pid or sec < 1000000000 or sec > now + 120 or usec >= 1000000:
    sys.exit(1)
print("%d %d %d %d" % (got, ppid, sec, usec))
};

# Returns the kinfo start identity for one pid: exactly 32 lowercase hex
# chars (two packed 64-bit little-endian integers: tv_sec, tv_usec), or undef.
sub darwin_bsd_start {
    my ($pid) = @_;
    return unless $^O eq 'darwin' && defined($pid) &&
        $pid =~ /\A[1-9][0-9]*\z/;
    my $child = open(my $fh, '-|');
    return unless defined($child);
    if (!$child) {
        open(STDERR, '>', '/dev/null');
        exec('python3', '-c', $DARWIN_BSDINFO_PY, $pid);
        exit 127;
    }
    my $line = <$fh>;
    close($fh) or return;
    return unless defined($line);
    chomp($line);
    my ($got, $ppid, $sec, $usec) = split(/ /, $line);
    return unless defined($got) && "$got" eq "$pid";
    return unpack('H*', pack('Q<Q<', $sec + 0, $usec + 0));
}

# The kinfo identity format is recognizable: exactly 32 lowercase hex chars.
# Legacy identities (hex of an lstart string, or of /proc clock-tick digits)
# never match that shape. The two formats must never be positively compared:
# a legacy claim checked against a kinfo table would demote a LIVE owner as a
# recycled leader. Mixed formats therefore fail closed (lock stays held).
sub kinfo_start_hex_p {
    my ($hex) = @_;
    return defined($hex) && $hex =~ /\A[0-9a-f]{32}\z/;
}

# (pid, ppid, pgid) rows for every process from one ps call. These are exact
# integer attributes of ps; only lstart had the whole-second problem, and the
# leader start time is deliberately NOT taken here -- it comes from
# darwin_bsd_start, the same source process_snapshot records, per the bug
# record's same-source rule.
sub darwin_ps_table {
    my $child = open(my $fh, '-|');
    return unless defined($child);
    if (!$child) {
        open(STDERR, '>', '/dev/null');
        exec('ps', '-axo', 'pid=,ppid=,pgid=');
        exit 127;
    }
    my @rows;
    while (my $line = <$fh>) {
        my ($pid, $ppid, $pgid) =
            $line =~ /^\s*([0-9]+)\s+([0-9]+)\s+([0-9]+)\s*$/;
        next unless defined($pid);
        push(@rows, [$pid + 0, $ppid + 0, $pgid + 0, undef]);
    }
    close($fh) or return;
    return @rows;
}

sub process_snapshot {
    my ($pid) = @_;
    return unless defined($pid) && $pid =~ /\A[1-9][0-9]*\z/;
    if ($^O eq 'darwin') {
        # Prefer the kinfo identity; on any failure fall through to the
        # legacy ps path, which keeps minting/checking comparable claims.
        my $start_one = darwin_bsd_start($pid);
        if (defined($start_one)) {
            my $pgid = ps_value('pgid', $pid);
            return unless defined($pgid) && $pgid =~ /\A[1-9][0-9]*\z/;
            my $start_two = darwin_bsd_start($pid);
            return unless defined($start_two) && $start_one eq $start_two;
            return ($start_one, $pgid);
        }
    }
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
#   - kill(0, -pgid) SUCCEEDED (same-uid group; the EPERM path is never
#     refined -- under hidepid another user's members are invisible and
#     demoting EPERM to dead would be the false-dead two-writers corruption
#     this lock exists to prevent),
#   - a process table is available. On Linux/MSYS/Cygwin that is the /proc
#     scan (field-22 clock ticks). On Darwin it is now a ps(1) pid/ppid/pgid
#     table plus a libproc kinfo start-time for the leader only -- never ps
#     lstart, whose whole-second resolution the 2026-09-12 bug record
#     measured as reclaiming live owners. Without either table the function
#     opts out and the kill()-based verdict stands (macOS before this port).
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
# Recorded and table start identities must share a FORMAT before case (b)
# can fire: a legacy claim (lstart-string or clock-tick hex) checked against
# a kinfo identity is incomparable and keeps the lock held (fail closed).
sub refine_leader_group_state {
    my ($pgid, $expected_start_hex) = @_;
    my $darwin = ($^O eq 'darwin');
    my @rows = $darwin ? darwin_ps_table() : proc_table();
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
    my $leader_start_hex;
    my $table_start_again;
    if ($darwin) {
        # The table row carries no start time (ps lstart is measured-unsafe);
        # read the leader's kinfo identity from the same source
        # process_snapshot records.
        $leader_start_hex = darwin_bsd_start($pgid);
        return 'live' unless defined($leader_start_hex);
        if (!kinfo_start_hex_p($expected_start_hex)) {
            print STDERR "portable-lock: recorded pgid $pgid claim carries " .
                "a legacy start identity that the kinfo start-time cannot " .
                "be compared against; keeping the lock held (fail closed)\n";
            return 'live';
        }
        $table_start_again = \&darwin_bsd_start;
    } else {
        $leader_start_hex = unpack('H*', $leader->[3]);
        $table_start_again = sub {
            my ($pid) = @_;
            my ($start) = proc_stat_snapshot($pid);
            return defined($start) ? unpack('H*', $start) : undef;
        };
    }
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
    # Re-read the leader's start-time through the SAME source the table used
    # (the bug record's trap: routing this through process_snapshot would mix
    # lstart with clock ticks and silently disable the reclaim on Linux).
    my $leader_start_again = $table_start_again->($pgid);
    return 'live' unless defined($leader_start_again) &&
        $leader_start_again eq $leader_start_hex;
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
