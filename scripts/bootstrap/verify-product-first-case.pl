#!/usr/bin/env perl
use strict;
use warnings;
use Digest::SHA qw(sha256_hex);

# A selected-case smoke is separate from full-registry qualification. The caller
# must first verify enumeration with verify-compiler-subsystem-test-product.pl.
@ARGV == 7 or die "usage: ENUMERATION EXECUTION CASE_ID PROCESS_EXIT WATCHDOG RSS_CAP RSS_MODE\n";
my ($enumeration, $execution, $chosen, $exit, $watchdog, $cap, $rss_mode) = @ARGV;
$chosen =~ /\A[0-9a-f]{64}\z/ && $exit =~ /\A\d+\z/ or die "invalid smoke identity/exit\n";
sub bytes {
    my ($path) = @_;
    -f $path && !-l $path && -s $path <= 134217728 or die "invalid bounded ledger\n";
    open my $f, '<:raw', $path or die "ledger unavailable\n";
    local $/; return <$f>;
}
my $enum = bytes($enumeration);
my $run = bytes($execution);
my $watch = bytes($watchdog);
my %watch_fields;
for my $line (split /\n/, $watch) {
    $line =~ /\A([a-zA-Z0-9_]+)=(.*)\z/ or die "invalid watchdog field\n";
    !exists $watch_fields{$1} or die "duplicate watchdog field\n";
    $watch_fields{$1} = $2;
}
($rss_mode eq 'monitor' || $rss_mode eq 'enforce') && $cap =~ /\A[1-9][0-9]*\z/ &&
    ($watch_fields{rss_cap_mode} // 'enforce') eq $rss_mode &&
    ($watch_fields{rss_cap_enforced} // '') eq ($rss_mode eq 'enforce' ? '1' : '0') &&
    ($watch_fields{rss_limit_kib} // '') eq ($rss_mode eq 'monitor' ? 'unlimited' : $cap) &&
    ($watch_fields{status} // '') eq 'complete' &&
    ($watch_fields{quiescent} // '') eq '1' &&
    ($watch_fields{observer_errors} // '') eq '0' &&
    ($watch_fields{exit_status} // '') eq $exit
    or die "watchdog resource/exit proof differs\n";
my @declared;
my @enum_shape;
for my $line (split /\n/, $enum) {
    if ($line =~ /\Adeclare\t([0-9a-f]{64})\t[0-9a-f]{64}\z/) { push @declared, $1; }
    push @enum_shape, $line unless $line =~ /\Acomplete\t/;
}
grep($_ eq $chosen, @declared) == 1 or die "chosen case absent or ambiguous\n";
my (@shape, @begins, @results, @trailers);
for my $line (split /\n/, $run) {
    if ($line =~ /\Abegin\t/) { push @begins, $line; }
    elsif ($line =~ /\Aresult\t/) { push @results, $line; }
    elsif ($line =~ /\Acomplete\t/) { push @trailers, $line; }
    else { push @shape, $line; }
}
join("\n", @shape) eq join("\n", @enum_shape) or die "smoke registration differs\n";
@trailers == 1 && $trailers[0] =~ /\Acomplete\tregistration_ok=1\ttest_callbacks_executed=(\d+)\thook_callbacks_executed=(\d+)\z/
    or die "smoke completion unavailable\n";
my ($callbacks, $hooks) = ($1, $2);
@results == 1 && $results[0] =~ /\Aresult\t\Q$chosen\E\t(pass|fail|skip|pending)\z/
    or die "smoke selector did not produce one exact result\n";
my $outcome = $1;
if ($outcome eq 'skip' && $callbacks == 0 && !@begins && $exit == 0) {
    print "status=SKIPPED\ncase_id=$chosen\n"; exit 3;
}
@begins == 1 && $begins[0] eq "begin\t$chosen" && $callbacks == 1
    or die "smoke did not execute exactly one real test callback\n";
($outcome eq 'pass' && $exit == 0) || ($outcome eq 'fail' && $exit == 1)
    or die "smoke process/result mismatch or nonexecuted pending case\n";
print "format=SIMPLE-PRODUCT-FIRST-CASE-1\nstatus=", ($outcome eq 'pass' ? 'PASS' : 'FAIL'),
    "\ncase_id=$chosen\nexecuted=1\nprocess_exit=$exit\n",
    "enumeration_sha256=", sha256_hex($enum), "\nexecution_sha256=", sha256_hex($run),
    "\nwatchdog_sha256=", sha256_hex($watch),
    "\nhook_callbacks_executed=$hooks\nfull_suite_count_contribution=0\n";
exit($outcome eq 'pass' ? 0 : 1);
