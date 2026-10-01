#!/usr/bin/perl
use strict;
use warnings;
use FindBin;
open my $fh, '<', "$FindBin::Bin/../../../scripts/resource/process-tree-rss-watchdog.pl" or die $!;
local $/;
my $source = <$fh>;
$source =~ s/\n# Workload startup boundary.*\z//s or die 'guard startup boundary missing';
local @ARGV = ('--', 'unused');
eval $source . <<'PROBE';
pipe(my $read, my $write) or die $!;
close $read;
# Exercise EPIPE deterministically before install/workload startup. Default
# SIGPIPE would terminate this test instead of reaching the assertion.
my $wrote = syswrite($write, "M\n");
die 'closed observer pipe accepted write' if defined $wrote;
close $write;
pipe($observer_read, my $feed) or die $!;
syswrite($feed, 'X' x 256);
close $feed;
eval { observer_line() };
die 'oversized protocol line not rejected' unless $@ =~ /oversized process observer row/;
close $observer_read;
print "PASS: pre-admission EPIPE and bounded protocol line\n";
PROBE
die $@ if $@;
