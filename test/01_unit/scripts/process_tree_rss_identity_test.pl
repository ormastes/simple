#!/usr/bin/perl
use strict;
use warnings;
use FindBin;
our @signals;
BEGIN {
    # No real process can be signaled by this PID/PGID-reuse simulation.
    *CORE::GLOBAL::kill = sub { push @signals, [@_]; return @_ - 1 };
}
open my $fh, '<', "$FindBin::Bin/../../../scripts/resource/process-tree-rss-watchdog.pl" or die $!;
local $/;
my $source = <$fh>;
$source =~ s/\n# Workload startup boundary.*\z//s or die 'guard startup boundary missing';
local @ARGV = ('--', 'unused');
my $probe = <<'PROBE';
$leader = 100;
%known = (100 => 'root', 200 => 'former-child');
%groups = (100 => 'root', 200 => 'former-child');
my $table = {
    100 => { parent => 1, group => 100, rss => 0, zombie => 1, identity => 'root' },
    200 => { parent => 1, group => 200, rss => 1, zombie => 0, identity => 'unrelated-reused-pid' },
};
signal_verified('STOP', $table);
signal_verified('KILL', $table);
for my $call (@main::signals) {
    die 'reused PID/PGID was signaled' if grep { abs($_) == 200 } @$call[1..$#$call];
}
@main::signals = ();
%known = (100 => 'root', 200 => 'former-child');
%groups = (100 => 'root', 200 => 'former-child');
{
    no warnings 'redefine';
    *snapshot = sub { die 'measurement unavailable' };
}
quiesce() == 0 or die 'failed measurement claimed quiescence';
for my $call (@main::signals) {
    die 'unvalidated cached identity was signaled' if grep { abs($_) != 100 } @$call[1..$#$call];
}
@main::signals = ();
%known = (100 => 'root');
%groups = (100 => 'root');
$identity_lost = 0;
{
    no warnings 'redefine';
    *snapshot = sub { return { 100 => $table->{100} } };
    *reap = sub { die 'root reaped before signaling finished' };
}
quiesce() == 1 or die 'empty anchored group did not quiesce';
print "PASS: PID/PGID reuse, failed identity sampling, unreaped root sentinel\n";
PROBE
eval $source . $probe;
die $@ if $@;
