#!/usr/bin/perl
use strict;
use warnings;
use Cwd qw(abs_path);
use File::Basename qw(dirname);
use File::Path qw(make_path);
use File::Spec;
use File::Temp qw(tempdir);
use FindBin qw($RealBin);

my $root = abs_path(File::Spec->catdir($RealBin, '..', '..', '..'));
my $watchdog = File::Spec->catfile($root, 'scripts', 'resource', 'process-tree-rss-watchdog.pl');
my $work = tempdir('rss-identity-publication.XXXXXX', TMPDIR => 1, CLEANUP => 1);
my $payload = "clang test identity\nTarget: x86_64-pc-windows-msvc\n";

sub check {
    my ($condition, $message) = @_;
    die "FAIL: $message\n" unless $condition;
}

sub publish_child {
    my ($identity_file, $identity, $barrier_dir, $label, $mode, $stderr_path) = @_;
    my $pid = fork();
    defined($pid) or die "cannot fork identity publisher: $!\n";
    if ($pid == 0) {
        open(STDERR, '>', $stderr_path) or die "cannot capture child stderr: $!\n";
        $ENV{SIMPLE_RSS_WATCHDOG_TEST_MODE} = '1';
        exec {$^X} $^X, $watchdog, '--test-identity-publication',
            $identity_file, $identity, $barrier_dir, $label, $mode;
        die "cannot exec watchdog identity publisher: $!\n";
    }
    return $pid;
}

sub wait_child {
    my ($pid) = @_;
    waitpid($pid, 0) == $pid or die "cannot wait for identity publisher $pid: $!\n";
    return $?;
}

sub has_temporary_files {
    my ($identity_file) = @_;
    my $dir = dirname($identity_file);
    my $leaf = (File::Spec->splitpath($identity_file))[2];
    opendir(my $dh, $dir) or die "cannot inspect identity directory $dir: $!\n";
    my @matches = grep { index($_, "$leaf.new.") == 0 } readdir($dh);
    closedir($dh) or die "cannot close identity directory $dir: $!\n";
    return scalar @matches;
}

sub read_bytes {
    my ($path) = @_;
    open(my $fh, '<:raw', $path) or die "cannot read $path: $!\n";
    local $/;
    my $value = <$fh>;
    close($fh) or die "cannot close $path: $!\n";
    return $value;
}

my $cold_dir = File::Spec->catdir($work, 'cold');
my $barrier = File::Spec->catdir($work, 'barrier');
make_path($cold_dir, $barrier);
my $cold_identity = File::Spec->catfile($cold_dir, 'identity.txt');
my @publishers = (
    publish_child($cold_identity, $payload, $barrier, 'left', 'race', File::Spec->catfile($work, 'left.err')),
    publish_child($cold_identity, $payload, $barrier, 'right', 'race', File::Spec->catfile($work, 'right.err')),
);
for (1 .. 3000) {
    last if -f File::Spec->catfile($barrier, 'left.ready') && -f File::Spec->catfile($barrier, 'right.ready');
    select(undef, undef, undef, 0.01);
}
check(-f File::Spec->catfile($barrier, 'left.ready') && -f File::Spec->catfile($barrier, 'right.ready'),
    'both cold-cache publishers reached the publication boundary');
open(my $go, '>', File::Spec->catfile($barrier, 'go')) or die "cannot open race barrier: $!\n";
close($go) or die "cannot close race barrier: $!\n";
check(wait_child($_) == 0, 'both concurrent same-identity publishers succeed') for @publishers;
check(read_bytes($cold_identity) eq $payload, 'published identity equals independently queried payload');
check(!has_temporary_files($cold_identity), 'successful publishers clean only their temporary files');

for my $case (
    ['divergent', 'clang' . ('z' x (length($payload) - length('clang'))), 'destination bytes differ from queried identity'],
    ['truncated', "clang\n", 'destination size or file type differs from queried identity'],
) {
    my ($label, $winner, $expected_error) = @$case;
    my $dir = File::Spec->catdir($work, $label);
    make_path($dir);
    my $identity_file = File::Spec->catfile($dir, 'identity.txt');
    open(my $existing, '>:raw', $identity_file) or die "cannot create negative control: $!\n";
    print {$existing} $winner or die "cannot write negative control: $!\n";
    close($existing) or die "cannot close negative control: $!\n";
    my $err = File::Spec->catfile($work, "$label.err");
    my $pid = publish_child($identity_file, $payload, '', $label, $label eq 'truncated' ? 'truncated' : 'corrupt', $err);
    check(wait_child($pid) != 0, "$label existing target is rejected");
    check(read_bytes($identity_file) eq $winner, "$label existing target is not overwritten");
    check(!has_temporary_files($identity_file), "$label rejection removes only caller temporary");
    check(index(read_bytes($err), $expected_error) >= 0,
        "$label rejection reports exact-winner mismatch");
}

my $missing_dir = File::Spec->catdir($work, 'missing');
make_path($missing_dir);
my $missing_identity = File::Spec->catfile($missing_dir, 'identity.txt');
my $missing_err = File::Spec->catfile($work, 'missing.err');
my $missing_pid = publish_child($missing_identity, $payload, '', 'missing', 'missing', $missing_err);
check(wait_child($missing_pid) != 0, 'publication failure with absent destination is rejected');
check(!-e $missing_identity, 'failed publication does not create an unverified target');
check(!has_temporary_files($missing_identity), 'absent-target failure cleans caller temporary');
check(index(read_bytes($missing_err), 'destination is absent') >= 0, 'absent-target failure is diagnosed');

print "PASS — concurrent identity publication and fail-closed winner controls\n";
