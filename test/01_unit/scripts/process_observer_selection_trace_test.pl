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
$leader = 100;
$session_id = 100;
%groups = (200 => 'old-anchor');
my $all = {
    100 => { parent => 1, group => 100, identity => 'root' },
    200 => { parent => 100, group => 200, identity => 'current-anchor' },
    300 => { parent => 200, group => 200, identity => 'child' },
};
my @trace;
local $SIG{__WARN__} = sub { push @trace, @_ };
eval { detail_eof(300, $all) };
die 'EOF not propagated' unless $@ =~ /incomplete process detail for PID 300 identity=child/;
die 'missing anchor evidence' unless $trace[0] eq
    "rss-guard: selection pid=300 root=100 session=100 group=200 retained_anchor=old-anchor current_anchor=current-anchor\n";
@trace == 4 or die 'incorrect ancestry length';
$trace[1] =~ /ancestry pid=300 ppid=200 pgid=200 identity=child/ or die 'missing child';
$trace[2] =~ /ancestry pid=200 ppid=100 pgid=200 identity=current-anchor/ or die 'missing parent';
$trace[3] =~ /ancestry pid=100 ppid=1 pgid=100 identity=root/ or die 'missing root';
$all->{200}{parent} = 300;
@trace = ();
eval { detail_eof(300, $all) };
@trace == 3 or die 'cyclic ancestry did not stop';
my %long = map { $_ => { parent => $_+1, group => 200, identity => "birth-$_" } } 300..350;
@trace = ();
eval { detail_eof(300, \%long) };
@trace == 33 or die 'ancestry diagnostic is not bounded to 32 rows';
print "PASS: selected process ancestry and anchor attribution; cycle/depth bounds\n";
PROBE
die $@ if $@;
