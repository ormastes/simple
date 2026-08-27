#!/usr/bin/env perl
use strict;
use warnings;
use Errno qw(EINTR EPERM);
use POSIX qw(setsid WIFEXITED WEXITSTATUS WIFSIGNALED WTERMSIG);

@ARGV or die "usage: portable-session-exec.pl PROGRAM [ARG...]\n";

sub current_group_identity {
    my ($pid) = @_;
    defined($pid) && "$pid" =~ /\A[1-9][0-9]*\z/ or return;
    my $pgid = getpgrp(0);
    defined($pgid) && "$pgid" =~ /\A[1-9][0-9]*\z/ or return;
    return ($pid, $pgid);
}

if ($ARGV[0] eq '--identity-current') {
    @ARGV == 1 or die "--identity-current takes no arguments\n";
    my @identity = current_group_identity($$);
    @identity == 2 or exit 1;
    print "pid=$identity[0]\npgid=$identity[1]\n";
    exit 0;
}

if ($ARGV[0] eq '--identity-parent') {
    @ARGV == 1 or die "--identity-parent takes no arguments\n";
    my $parent = getppid();
    my @identity = current_group_identity($parent);
    @identity == 2 && getppid() == $parent or exit 1;
    print "pid=$identity[0]\npgid=$identity[1]\n";
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

my $session = setsid();
if (defined($session) && $session >= 0) {
    die "setsid unexpectedly succeeded while fallback was required\n"
        if $require_fallback;
    exec_program();
}
die "setsid failed: $!\n" unless $! == EPERM;

# A process-group leader cannot call setsid. Fork once in that exceptional
# launch shape; the child becomes the session leader and execs immediately.
my $child = fork();
defined($child) or die "fork failed: $!\n";
if ($child == 0) {
    setsid() >= 0 or die "child setsid failed: $!\n";
    exec_program();
}

for my $signal (qw(HUP INT TERM QUIT)) {
    $SIG{$signal} = sub { kill($signal, -$child); };
}

my $waited;
do {
    $waited = waitpid($child, 0);
} while ($waited < 0 && $! == EINTR);
$waited == $child or die "waitpid failed: $!\n";
exit WEXITSTATUS($?) if WIFEXITED($?);
exit 128 + WTERMSIG($?) if WIFSIGNALED($?);
exit 1;
