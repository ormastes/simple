#!/usr/bin/env perl
use strict;
use warnings;
use File::Path qw(make_path remove_tree);
use File::Temp qw(tempdir);
use FindBin qw($Bin);
use Test::More;

my $package = "$Bin/../../..";
my $coordinator = "$package/scripts/check/lib/bootstrap-stage23-coordinator.pl";
my $fixture = "$package/test/fixtures/stage23-coordinator/fake-phase.shs";
my @roles = qw(perl dash env unit_supervisor unit_gate stage2_runner session
    planner_admission cache_policy jobs_policy provenance_facade
    provenance_authority provenance_command provenance_sanity
    provenance_manifest_write provenance_manifest_verify provenance_self_test
    portable_lock_atomic portable_process_lock authority_wiring stage4_provenance
    resume_stage4 progress_watch platform_detect candidate_frontend preserve_phase
    stage2_receiver stage_log compiler_deadline planner_producer planner_verifier
    planner_source shared_runner preexec_gate runner_adapter sampler analyzer
    bootstrap_script provenance_verifier facade session_helper
    candidate_builder);

sub setup_case {
    my ($mode) = @_;
    my $tmp = tempdir(CLEANUP => 1);
    make_path("$tmp/root", "$tmp/roles", "$tmp/cgroup", "$tmp/resume");
    my @bindings;
    for my $role (@roles) {
        my $path = "$tmp/roles/$role";
        open(my $in, '<', $fixture) or die $!; open(my $out, '>', $path) or die $!;
        while (read($in, my $buf, 65536)) { print {$out} $buf or die $!; }
        close($in); close($out); chmod($role eq 'planner_source' ? 0600 : 0700, $path);
        push @bindings, "--role=$role=$path";
    }
    my @cmd = ($^X, $coordinator, "--mode=$mode", "--root=$tmp/root",
        "--transaction-root=$tmp/result", '--architecture=x86_64-unknown-linux-gnu',
        '--run-id=fixture_1234', '--reason=//bootstrap:stage3:fixture',
        "--heavy-lock=$tmp/lock", "--owner-journal=$tmp/owner",
        "--quarantine=$tmp/quarantine", "--systemd-run=$tmp/roles/unit_supervisor",
        "--systemctl=$tmp/roles/unit_gate", "--cgroup-root=$tmp/cgroup",
        '--allow-test-hooks', @bindings);
    push @cmd, $mode eq 'fresh' ? "--stage2-bootstrap=$tmp/roles/candidate_builder" :
        "--resume-stage2-transaction=$tmp/resume";
    return ($tmp, \@cmd);
}
sub run_case {
    my ($cmd, $extra) = @_;
    local %ENV = (%ENV, STAGE23_FIXTURE_RUN_ID => 'fixture_1234',
        STAGE23_FIXTURE_ARCH => 'x86_64-unknown-linux-gnu', %{$extra // {}});
    system(@$cmd); return $? >> 8;
}

for my $mode (qw(fresh resume)) {
    my ($tmp, $cmd) = setup_case($mode);
    is(run_case($cmd), 0, "$mode path commits");
    ok(-f "$tmp/result/coordinator.env", "$mode publishes coordinator receipt");
    open(my $fh, '<', "$tmp/result/coordinator.env") or die $!;
    my $text = do { local $/; <$fh> }; close($fh);
    like($text, qr/^schema=simple-stage23-transaction-admission-v1$/m, 'final schema');
    like($text, qr/^compatibility_authority=false$/m, 'compatibility is non-authority');
}
{
    my ($tmp, $cmd) = setup_case('fresh');
    is(run_case($cmd, { STAGE23_FIXTURE_FAIL_PHASE => 'planner' }), 71,
        'planner failure is terminal');
    ok(!-e "$tmp/result", 'failed transaction is not published');
    my @staging = glob("$tmp/.result.stage23.*");
    is(scalar(@staging), 0, 'failed transaction staging is cleaned');
}
{
    my ($tmp, $cmd) = setup_case('fresh');
    mkdir "$tmp/result" or die $!;
    isnt(run_case($cmd), 0, 'destination collision rejected');
}
{
    my ($tmp, $cmd) = setup_case('fresh');
    my ($a) = grep { /^--role=perl=/ } @$cmd;
    my ($b_index) = grep { $cmd->[$_] =~ /^--role=dash=/ } 0..$#$cmd;
    (my $path = $a) =~ s/^--role=perl=//;
    $cmd->[$b_index] = "--role=dash=$path";
    isnt(run_case($cmd), 0, 'executable alias rejected');
}
done_testing();
