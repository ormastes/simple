#!/usr/bin/env perl
use strict;
use warnings;
use Errno qw(EINTR);
use Fcntl qw(F_GETFD F_SETFD FD_CLOEXEC O_RDONLY);
use POSIX ();

# The unit supervisor starts this helper with the service's stdin connected to
# its one-byte launch gate.  Nothing in the payload may run until the parent has
# retained and checked the cgroup authority files and durably published the
# unit launch plan.
@ARGV >= 2 && $ARGV[0] eq '--'
    or die "stage3 pre-exec gate: expected -- and a payload\n";
shift @ARGV;

my $payload = $ARGV[0];
$payload =~ m{\A/proc/[1-9][0-9]*/fd/[0-9]+\z}
    or die "stage3 pre-exec gate: payload is not a retained descriptor\n";

sysopen(my $payload_fh, $payload, O_RDONLY)
    or die "stage3 pre-exec gate: open payload descriptor: $!\n";
my @payload_stat = stat($payload_fh);
@payload_stat && -f _
    or die "stage3 pre-exec gate: payload descriptor is not regular\n";
my $fd_flags = fcntl($payload_fh, F_GETFD, 0);
defined($fd_flags) or die "stage3 pre-exec gate: read descriptor flags: $!\n";
fcntl($payload_fh, F_SETFD, $fd_flags | FD_CLOEXEC)
    or die "stage3 pre-exec gate: set close-on-exec: $!\n";

my $gate = '';
while (length($gate) < 1) {
    my $read = sysread(STDIN, $gate, 1 - length($gate), length($gate));
    if (!defined($read)) {
        next if $! == EINTR;
        die "stage3 pre-exec gate: read launch gate: $!\n";
    }
    $read > 0 or die "stage3 pre-exec gate: launch gate closed\n";
}
$gate eq 'G' or die "stage3 pre-exec gate: invalid launch byte\n";
close(STDIN) or die "stage3 pre-exec gate: close launch gate: $!\n";

$SIG{HUP} = $SIG{INT} = $SIG{QUIT} = $SIG{TERM} = $SIG{CHLD} = 'DEFAULT';
my $bound_payload = '/proc/self/fd/' . fileno($payload_fh);
exec {$bound_payload} @ARGV;
POSIX::_exit(126);
