#!/usr/bin/perl
use strict;
use warnings;
use FindBin;
use File::Temp qw(tempdir);

# Exercise the production finalization and receipt writer, with no real process
# signals. A deterministic failed cleanup represents the opus-10 RSS breach.
open my $fh, '<', "$FindBin::Bin/../../../scripts/resource/process-tree-rss-watchdog.pl" or die $!;
local $/;
my $source = <$fh>;
my ($finalize) = $source =~ /(my \(\$primary_status, \$primary_code\).*?)\nexit \$code;\s*\z/s;
defined($finalize) or die 'guard finalization boundary missing';
$source =~ s/\n# Workload startup boundary.*\z//s or die 'guard startup boundary missing';
my $work = tempdir(CLEANUP => 1);
local @ARGV = ("--receipt=$work/receipt.env", '--', 'unused');
open my $diagnostics, '>', "$work/diagnostics.log" or die $!;

my $probe = <<'PROBE';
{
    no warnings 'redefine';
    *quiesce = sub { return $main::test_quiet };
    *stop_observer = sub { };
    *reap = sub { };
}
my @cases = (
    ['rss-cap-exceeded', 88, 0, 0, 'rss-containment-unverified', 89, 'rss-cap-exceeded', 88],
    ['timeout', 124, 0, 0, 'rss-containment-unverified', 89, 'timeout', 124],
    ['rss-measurement-failed', 89, 0, 0, 'rss-measurement-failed', 89, 'rss-measurement-failed', 89],
    ['rss-cap-exceeded', 88, 1, 0, 'rss-cap-exceeded', 88, 'rss-cap-exceeded', 88],
    ['complete', 0, 1, 7 << 8, 'complete', 7, 'complete', 7],
    ['complete', 0, 1, 0, 'complete', 0, 'complete', 0],
);
for my $case (@cases) {
    my ($status, $code) = @$case;
    $main::test_quiet = $case->[2];
    $child_status = $case->[3];
PROBE
$probe .= $finalize;
$probe .= <<'PROBE';
    open my $result, '<', $opt{receipt} or die $!;
    my $receipt = do { local $/; <$result> };
    for my $pair (['status', 4], ['exit_status', 5], ['primary_status', 6], ['primary_exit_status', 7]) {
        my ($key, $index) = @$pair;
        $receipt =~ /^\Q$key=$case->[$index]\E$/m or die "case @$case missing $key";
    }
    $code == $case->[5] or die 'process verdict changed';
}
print "PASS: 6 primary-failure receipt cases; containment remains fail-closed\n";
PROBE
my $error;
{
    local *STDERR = $diagnostics;
    eval $source . $probe;
    $error = $@;
}
die $error if $error;
