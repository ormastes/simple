#!/usr/bin/env perl
use strict;
use warnings;
use Cwd qw(realpath);
use Digest::SHA ();
use File::Basename qw(dirname);
use File::Copy qw(copy);
use File::Find ();
use File::Path qw(remove_tree);
use File::Spec ();
use JSON::PP ();

sub fail { die "native-aot-evidence: $_[0]\n" }
@ARGV == 11 or fail('expected log, private tmp, source root, suite, backend, compiler, producer SHA, threads, runtime path, runtime identity, receipt');
my ($log, $tmp, $root, $suite, $backend, $compiler, $producer_sha, $threads,
    $runtime_path, $runtime_identity, $receipt) = @ARGV;
$backend =~ /\A(?:llvm|cranelift)\z/ or fail('invalid backend');
$producer_sha =~ /\A[0-9a-f]{64}\z/ or fail('invalid producer SHA');
$threads =~ /\A[1-9][0-9]*\z/ or fail('invalid thread count');
$runtime_identity =~ /\A[0-9a-f]{64}\z/ or fail('invalid runtime identity');
-f $log && !-l $log or fail('runner log missing or linked');
-d $tmp && !-l $tmp or fail('private TMPDIR missing or linked');

sub hash_file {
    my ($path) = @_;
    open my $fh, '<:raw', $path or fail("cannot read $path");
    my $digest = Digest::SHA->new(256);
    $digest->addfile($fh);
    close $fh or fail("cannot close $path");
    return $digest->hexdigest;
}
hash_file($compiler) eq $producer_sha or fail('producer bytes changed before evidence validation');

open my $fh, '<:raw', $log or fail('cannot read runner log');
my (@terminal_json, @invocations, %running, @results);
while (my $line = <$fh>) {
    $line =~ s/\r?\n\z//;
    push @terminal_json, $line if $line =~ /^\{"success":/;
    if ($line =~ /^native-aot-invocation\|(\{.*\})\z/) {
        my $item = eval { JSON::PP::decode_json($1) };
        !$@ && ref($item) eq 'HASH' or fail('malformed native invocation JSON');
        push @invocations, $item;
    }
    $running{$1}++ if $line =~ /^\[native\] Running (.+)\z/;
    push @results, $line if $line =~ /^Results:/;
    $line !~ /\b(?:mcdc-fallback|coverage-fallback|interpreter-fallback)\b/ or
        fail('native row used a fallback');
}
close $fh or fail('cannot close runner log');
@terminal_json == 1 or fail('expected exactly one terminal JSON result');
@results == 1 or fail('expected exactly one Results receipt');
my $row = eval { JSON::PP::decode_json($terminal_json[0]) };
!$@ && ref($row) eq 'HASH' && ref($row->{spec}) eq 'HASH' or fail('invalid terminal JSON result');
my $spec_result = $row->{spec};
$row->{success} && $spec_result->{success} or fail('test runner reported failure');
ref($spec_result->{files}) eq 'ARRAY' or fail('terminal JSON has no file inventory');
my @files = @{$spec_result->{files}};
@files > 0 or fail('empty file inventory');
@invocations == @files or fail('native invocation count differs from test file count');
my ($results_total, $results_passed, $results_failed) =
    $results[0] =~ /^Results: ([0-9]+) total, ([0-9]+) passed, ([0-9]+) failed/;
defined $results_total && $results_total > 0 && $results_failed == 0 &&
    $results_passed == $results_total or fail('nonpassing or malformed Results receipt');

my %expected;
my $suite_path = File::Spec->catfile($root, $suite);
if (-d $suite_path) {
    File::Find::find({ no_chdir => 1, wanted => sub {
        return unless -f $File::Find::name && $File::Find::name =~ /_spec\.spl\z/;
        my $rel = File::Spec->abs2rel($File::Find::name, $root);
        $rel =~ s{\\}{/}g;
        $expected{$rel}++;
    } }, $suite_path);
} elsif (-f $suite_path) {
    $expected{$suite}++;
} else {
    fail('suite path is missing');
}
keys(%expected) == @files or fail('runner omitted or added suite files');

my %files_by_path;
my $sum_passed = 0;
for my $file (@files) {
    ref($file) eq 'HASH' or fail('malformed file result');
    my $path = $file->{path} // '';
    $expected{$path} == 1 && !$files_by_path{$path}++ or fail("unexpected or duplicate file result: $path");
    ($file->{passed} // 0) > 0 && ($file->{failed} // -1) == 0 &&
        ($file->{skipped} // -1) == 0 && ($file->{pending} // -1) == 0 &&
        !defined($file->{error}) or fail("file has no executed passing assertions: $path");
    $sum_passed += $file->{passed};
}
$sum_passed == $results_total && $sum_passed == ($spec_result->{total_passed} // -1) or
    fail('per-file assertions disagree with aggregate Results');

my $tmp_real = realpath($tmp) // fail('cannot resolve private TMPDIR');
my $producer_prefix = substr($producer_sha, 0, 16);
my %artifact_paths;
my %invocation_specs;
my @artifact_rows;
for my $item (@invocations) {
    my $spec = $item->{spec} // '';
    my $output = $item->{output} // '';
    my $argv = $item->{argv};
    $files_by_path{$spec} == 1 or fail("invocation has no passing file result: $spec");
    !$invocation_specs{$spec}++ or fail("duplicate native invocation for $spec");
    !$artifact_paths{$output}++ or fail('duplicate output artifact');
    ($item->{backend} // '') eq $backend or fail('invocation backend differs');
    ($item->{producer_sha256} // '') eq $producer_sha or fail('invocation producer differs');
    ($item->{compiler} // '') eq $compiler or fail('invocation compiler differs');
    ref($argv) eq 'ARRAY' && @$argv > 2 && $argv->[0] eq 'native-build' or fail('not a native-build invocation');
    my %opt;
    for (my $i = 1; $i < @$argv; $i++) {
        if ($argv->[$i] =~ /^--(?:backend|threads|output|entry|source|runtime-bundle|runtime-path|cache-dir)$/) {
            $i + 1 < @$argv or fail('truncated native-build argv');
            push @{$opt{$argv->[$i]}}, $argv->[$i + 1];
            $i++;
        } elsif ($argv->[$i] eq '--entry-closure' || $argv->[$i] eq '--verbose') {
            $opt{$argv->[$i]} = 1;
        } else {
            fail('unexpected native-build argv token');
        }
    }
    for my $required ('--backend', '--threads', '--output', '--entry', '--source', '--runtime-bundle', '--cache-dir') {
        ref($opt{$required}) eq 'ARRAY' && @{$opt{$required}} == 1 or fail("missing or duplicate $required");
    }
    $opt{'--backend'}[0] eq $backend or fail('actual compiler argv backend differs');
    $opt{'--threads'}[0] eq $threads or fail('actual compiler argv threads differ');
    $opt{'--output'}[0] eq $output or fail('actual compiler argv output differs');
    $opt{'--cache-dir'}[0] eq "$output.cache" or fail('actual compiler argv cache differs');
    if ($runtime_path ne '') {
        ref($opt{'--runtime-path'}) eq 'ARRAY' && @{$opt{'--runtime-path'}} == 1 &&
            $opt{'--runtime-path'}[0] eq $runtime_path or fail('actual compiler argv runtime path differs');
    } else {
        !exists $opt{'--runtime-path'} or fail('unexpected compiler runtime path');
    }
    $opt{'--source'}[0] eq 'src/lib' && $opt{'--runtime-bundle'}[0] eq 'core-c-bootstrap' &&
        $opt{'--entry-closure'} or fail('native-build closure/runtime arguments differ');
    $output =~ m{\A\Q$tmp_real\E/} or fail('artifact escaped private TMPDIR');
    -f $output && !-l $output && -x $output or fail("native artifact missing or not executable: $output");
    (realpath($output) // '') =~ m{\A\Q$tmp_real\E/} or fail('artifact resolves outside private TMPDIR');
    $output =~ /\Q$backend\E/ && $output =~ /\Q$producer_prefix\E/ or
        fail('artifact filename lacks backend/producer identity');
    $running{$output} == 1 or fail('artifact was not logged as executed exactly once');
    open my $artifact, '<:raw', $output or fail('cannot read artifact header');
    read($artifact, my $magic, 4) == 4 or fail('short artifact');
    close $artifact or fail('cannot close artifact');
    ($magic eq "\x7fELF" || substr($magic, 0, 2) eq 'MZ' ||
        $magic =~ /\A(?:\xfe\xed\xfa[\xce\xcf]|\xcf\xfa\xed\xfe|\xca\xfe\xba\xbe)/s) or
        fail('artifact is not a native executable image');
    push @artifact_rows, [$spec, $output, hash_file($output)];
}
scalar(keys %running) == @artifact_rows or fail('unexpected additional native execution');
scalar(keys %invocation_specs) == @files or fail('native invocation/file inventory is not bijective');
hash_file($compiler) eq $producer_sha or fail('producer bytes changed after evidence validation');

my $sample = File::Spec->catfile(dirname($tmp), 'sample-artifact');
copy($artifact_rows[0][1], $sample) or fail('cannot retain sample artifact');
chmod 0500, $sample or fail('cannot protect sample artifact');
hash_file($sample) eq $artifact_rows[0][2] or fail('retained sample hash differs');
open my $out, '>:raw', $receipt or fail('cannot write evidence receipt');
print $out "schema=simple-native-aot-suite-evidence-v1\nbackend=$backend\nproducer_sha256=$producer_sha\n";
print $out "compiler=$compiler\nthreads=$threads\nruntime_path=$runtime_path\nruntime_identity_sha256=$runtime_identity\nsuite=$suite\nfile_count=" . scalar(@files) . "\nassertions_passed=$sum_passed\n";
print $out "sample_artifact=$sample\nsample_artifact_sha256=$artifact_rows[0][2]\n";
print $out "spec\tartifact\tartifact_sha256\n";
for my $row (@artifact_rows) { print $out join("\t", @$row), "\n"; }
close $out or fail('cannot close evidence receipt');
chmod 0400, $receipt or fail('cannot protect evidence receipt');
my $cleanup_errors;
remove_tree($tmp, { error => \$cleanup_errors });
(!$cleanup_errors || @$cleanup_errors == 0) && !-e $tmp or
    fail('cannot clean verified transient native artifacts');
print "native-aot-evidence: PASS backend=$backend files=" . scalar(@files) . " assertions=$sum_passed receipt=$receipt\n";
