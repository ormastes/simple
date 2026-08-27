#!/usr/bin/env perl
use strict;
use warnings;
use Errno qw(ECHILD EINTR EPERM ESRCH);
use Digest::SHA qw(sha256_hex);
use POSIX qw(setsid WNOHANG WIFEXITED WEXITSTATUS WIFSIGNALED WTERMSIG);
use Time::HiRes qw(clock_gettime CLOCK_MONOTONIC sleep);

@ARGV or die "usage: portable-session-exec.pl PROGRAM [ARG...]\n";

sub proc_identity {
    my ($pid, $force_portable) = @_;
    defined($pid) && "$pid" =~ /\A[1-9][0-9]*\z/ or return;
    return portable_ps_identity($pid) if $force_portable;
    open(my $stat, '<', "/proc/$pid/stat") or return portable_ps_identity($pid);
    my $line = <$stat>;
    close($stat) or return;
    defined($line) && $line =~ s/\A[0-9]+ \(.*\) // or return;
    my @field = split(/ /, $line);
    @field >= 20 or return;
    my ($ppid, $pgid, $sid, $start) = @field[1, 2, 3, 19];
    for ($ppid, $pgid, $sid, $start) {
        defined($_) && /\A[1-9][0-9]*\z/ or return;
    }
    return ($pid, $ppid, $pgid, $start, $sid);
}

sub portable_ps_identity {
    my ($pid) = @_;
    my $ps = -x '/bin/ps' ? '/bin/ps' : -x '/usr/bin/ps' ? '/usr/bin/ps' : return;
    # Darwin's `sess` value is an opaque kernel pointer, not a numeric SID.
    # The portable identity therefore binds only fields whose meaning ps
    # specifies on both Darwin and BSD/GNU hosts.  SID is deliberately absent
    # on this path and is emitted only from numeric /proc authority above.
    open(my $pipe, '-|', $ps, '-p', $pid, '-o', 'pid=', '-o', 'ppid=',
         '-o', 'pgid=', '-o', 'lstart=')
        or return;
    my $line = <$pipe>;
    close($pipe) or return;
    defined($line) or return;
    $line =~ s/\A\s+//;
    $line =~ s/\s+\z//;
    my ($observed_pid, $ppid, $pgid, $started) = split(/\s+/, $line, 4);
    defined($observed_pid) && $observed_pid eq "$pid" or return;
    defined($ppid) && $ppid =~ /\A[1-9][0-9]*\z/ or return;
    defined($pgid) && $pgid =~ /\A[1-9][0-9]*\z/ or return;
    defined($started) && length($started) or return;
    return ($pid, $ppid, $pgid, sha256_hex($started), undef);
}

sub stable_identity {
    my ($pid, $force_portable) = @_;
    my @first = proc_identity($pid, $force_portable);
    @first == 5 or return;
    my @second = proc_identity($pid, $force_portable);
    @second == 5 or return;
    for my $index (0 .. 3) {
        defined($first[$index]) && defined($second[$index]) &&
            $first[$index] eq $second[$index] or return;
    }
    ((!defined($first[4]) && !defined($second[4])) ||
     (defined($first[4]) && defined($second[4]) &&
      $first[4] eq $second[4])) or return;
    return @first;
}

sub print_identity {
    my (@identity) = @_;
    print "pid=$identity[0]\nppid=$identity[1]\npgid=$identity[2]\n";
    print "sid=$identity[4]\n" if defined($identity[4]);
    print "start=$identity[3]\n";
}

if ($ARGV[0] eq '--identity-current') {
    @ARGV == 1 or die "--identity-current takes no arguments\n";
    my @identity = stable_identity($$);
    @identity == 5 or exit 1;
    print_identity(@identity);
    exit 0;
}

if ($ARGV[0] eq '--identity-parent') {
    @ARGV == 1 or die "--identity-parent takes no arguments\n";
    my $parent = getppid();
    my @identity = stable_identity($parent);
    @identity == 5 && getppid() == $parent or exit 1;
    print_identity(@identity);
    exit 0;
}

if ($ARGV[0] eq '--test-portable-identity-current') {
    @ARGV == 1 or die "--test-portable-identity-current takes no arguments\n";
    my @identity = stable_identity($$, 1);
    @identity == 5 && !defined($identity[4]) or exit 1;
    print_identity(@identity);
    exit 0;
}

my $require_fallback = 0;
if ($ARGV[0] eq '--require-fallback') {
    shift(@ARGV);
    @ARGV or die "--require-fallback requires PROGRAM [ARG...]\n";
    $require_fallback = 1;
}

sub exec_program {
    for my $signal (qw(HUP INT TERM QUIT)) {
        $SIG{$signal} = 'DEFAULT';
    }
    exec {$ARGV[0]} @ARGV or die "exec $ARGV[0] failed: $!\n";
}

# The wrapper is the sole wait-status owner.  A launcher may have inherited
# SIGCHLD=IGNORE or SA_NOCLDWAIT; resetting the disposition before either the
# direct exec or fallback fork restores ordinary child status semantics.
$SIG{CHLD} = 'DEFAULT';

my $session = setsid();
if (defined($session) && $session >= 0) {
    die "setsid unexpectedly succeeded while fallback was required\n"
        if $require_fallback;
    exec_program();
}
die "setsid failed: $!\n" unless $! == EPERM;

my $requested_signal;
my %signal_priority = (TERM => 1, INT => 2, HUP => 3, QUIT => 4);
for my $signal (qw(HUP INT TERM QUIT)) {
    $SIG{$signal} = sub {
        $requested_signal = $signal
            if !defined($requested_signal) ||
               $signal_priority{$signal} < $signal_priority{$requested_signal};
    };
}

# A process-group leader cannot call setsid. Fork once in that exceptional
# launch shape; the child becomes the session leader and execs immediately.
# Handlers are installed before fork, closing the cancellation gap; the child
# restores defaults in exec_program before entering the measured payload.
my $child = fork();
defined($child) or die "fork failed: $!\n";
if ($child == 0) {
    setsid() >= 0 or die "child setsid failed: $!\n";
    exec_program();
}

my ($forwarded, $killed, $deadline);
my $waited = 0;
while ($waited == 0) {
    if (defined($requested_signal) && !$forwarded) {
        kill($requested_signal, -$child) or $! == ESRCH or die "signal child session failed: $!\n";
        $forwarded = 1;
        $deadline = clock_gettime(CLOCK_MONOTONIC) + 2.0;
    }
    if ($forwarded && !$killed && clock_gettime(CLOCK_MONOTONIC) >= $deadline) {
        kill('KILL', -$child) or $! == ESRCH or die "kill child session failed: $!\n";
        $killed = 1;
        $deadline = clock_gettime(CLOCK_MONOTONIC) + 2.0;
    }
    if ($killed && clock_gettime(CLOCK_MONOTONIC) >= $deadline) {
        die "child session did not reap after SIGKILL\n";
    }
    $waited = waitpid($child, WNOHANG);
    if ($waited < 0) {
        next if $! == EINTR;
        die "waitpid lost child identity\n" if $! == ECHILD;
        die "waitpid failed: $!\n";
    }
    sleep(0.01) if $waited == 0;
}
$waited == $child or die "waitpid failed: $!\n";
exit WEXITSTATUS($?) if WIFEXITED($?);
exit 128 + WTERMSIG($?) if WIFSIGNALED($?);
exit 1;
