#!/usr/bin/env perl
use strict;
use warnings;
use Fcntl qw(:DEFAULT :flock F_GETFD F_SETFD FD_CLOEXEC);
use File::Basename qw(dirname);
use File::Path qw(make_path);
use File::Temp qw(tempdir);
use Test::More;

my $package = $ENV{STAGE2_RUNNER_PACKAGE} or die "STAGE2_RUNNER_PACKAGE required\n";
my $runner = "$package/scripts/check/lib/bootstrap-stage2-runner.pl";
my $bootstrap = "$package/test/00_unit/scripts/fake-stage2-bootstrap.shs";
my $helper_fixture = "$package/test/00_unit/scripts/fake-stage2-helper-capsule.shs";
my @helper_names = qw(session planner_admission cache_policy jobs_policy
    provenance_facade provenance_authority provenance_command provenance_sanity
    provenance_manifest_write provenance_manifest_verify provenance_self_test
    portable_lock_atomic portable_process_lock authority_wiring stage4_provenance
    resume_stage4 progress_watch platform_detect candidate_frontend preserve_phase
    stage2_receiver stage_log compiler_deadline);

sub inheritable {
    my ($fh) = @_;
    my $flags = fcntl($fh, F_GETFD, 0);
    fcntl($fh, F_SETFD, $flags & ~FD_CLOEXEC) or die $!;
}
sub invoke {
    my ($base, %change) = @_;
    my $parent = "$base/parents"; make_path($parent, { mode => 0700 });
    my $transaction = "$parent/stage2.transaction";
    my %target = (transaction => $transaction,
        output => "$transaction/output", evidence => "$transaction/evidence",
        home => "$transaction/home", tmp => "$transaction/tmp",
        cache => "$transaction/cache", legacy_out => "$parent/out",
        legacy_evidence => "$parent/evidence");
    if ($change{collision}) {
        mkdir($transaction, 0700) or die $!;
    }
    my $lock_path = "$parent/heavy.lock";
    sysopen(my $lock, $lock_path, O_RDWR | O_CREAT | O_NOFOLLOW, 0600) or die $!;
    my $unrelated_lock;
    if ($change{forged_unrelated_lock}) {
        sysopen($unrelated_lock, $lock_path, O_RDWR | O_NOFOLLOW) or die $!;
        flock($unrelated_lock, LOCK_EX | LOCK_NB) or die $!;
    } elsif (!$change{unlocked}) {
        flock($lock, LOCK_EX | LOCK_NB) or die $!;
    }
    inheritable($lock);
    open(my $bootstrap_fd, '<', $bootstrap) or die $!;
    inheritable($bootstrap_fd);
    my $bootstrap_role = "/proc/$$/fd/" . fileno($bootstrap_fd);
    my $helper_parent = "$parent/helper-authority";
    make_path($helper_parent, { mode => 0700 });
    my $helper_path = "$helper_parent/helper";
    open(my $fixture, '<', $helper_fixture) or die $!;
    open(my $helper_copy, '>', $helper_path) or die $!;
    while (read($fixture, my $bytes, 8192)) { print {$helper_copy} $bytes or die $!; }
    close($fixture); close($helper_copy);
    open(my $helper_fd, '<', $helper_path) or die $!;
    inheritable($helper_fd);
    my $helper_role = "/proc/$$/fd/" . fileno($helper_fd);
    if ($change{mutate_helper_authority}) {
        unlink($helper_path) or die $!;
        open(my $replacement, '>', $helper_path) or die $!;
        print {$replacement} "mutable-leaf-replacement\n" or die $!;
        close($replacement);
        rename($helper_parent, "$parent/mutated-helper-ancestor") or die $!;
        make_path($helper_parent, { mode => 0700 });
    }
    local %ENV = (%ENV, SIMPLE_STAGE3_OUTER_LOCK_HELD => '1',
        SIMPLE_STAGE3_HEAVY_LOCK_CAPABILITY_FD => '' . fileno($lock),
        SIMPLE_BOOTSTRAP_BUILD_JOBS => '16',
        SIMPLE_BOOTSTRAP_MAX_BUILD_JOBS => '16',
        SIMPLE_NO_STUB_FALLBACK => '1', %{delete($change{env}) // {}});
    local $ENV{FAKE_STAGE2_BEHAVIOR} = $change{behavior} // 'success';
    local $ENV{STAGE2_RUNNER_TEST_CHILD_FAIL} = $change{child_fail} // '';
    my @args = ('/usr/bin/perl', $runner, "--root=$package",
        "--transaction-root=$transaction",
        "--bootstrap=$bootstrap_role", '--compiler-wall-ms=500',
        '--memory-max=53687091200', "--outer-lock-fd=" . fileno($lock),
        "--outer-lock-path=$lock_path", '--allow-test-hooks');
    push @args, map { "--helper=$_=$helper_role" } @helper_names;
    push @args, "--dash=$change{dash}" if $change{dash};
    push @args, "--memory-max=$change{memory}" if $change{memory};
    push @args, '--outer-lock-fd=9999' if $change{bad_fd};
    push @args, '--stage2-wall-ms=500' if $change{legacy_stage2_wall};
    push @args, '--output=/legacy/sibling' if $change{legacy_output};
    my $status;
    if ($change{wrong_cwd}) {
        my $pid = fork(); defined($pid) or die $!;
        if (!$pid) {
            chdir($base) or exit 126;
            exec @args;
            exit 127;
        }
        waitpid($pid, 0) == $pid or die $!;
        $status = $?;
    } else {
        system(@args);
        $status = $?;
    }
    return ($status >> 8, \%target);
}

my ($code, $target) = invoke(tempdir(CLEANUP => 1));
if (-f "$target->{evidence}/fd-leak.env") {
    open(my $leak, '<', "$target->{evidence}/fd-leak.env") or die $!;
    my $detail = do { local $/; <$leak> }; close($leak);
    diag($detail);
}
is($code, 0, 'descriptor-pinned supervisor role succeeds');
ok(-d $target->{transaction}, 'one initially absent transaction root is published');
ok(-d $target->{output} && -d $target->{evidence} && -d $target->{home} &&
        -d $target->{tmp} && -d $target->{cache},
    'transaction contains exactly the fixed mutable child authorities');
ok(!-e $target->{legacy_out} && !-e $target->{legacy_evidence},
    'no legacy output or evidence sibling alias is published');
open(my $transaction_fh, '<', "$target->{transaction}/transaction.env") or die $!;
my $transaction_receipt = do { local $/; <$transaction_fh> };
close($transaction_fh);
like($transaction_receipt,
    qr/^schema=simple-bootstrap-stage2-transaction-v1$/m,
    'transaction receipt has the frozen schema');
like($transaction_receipt, qr/^status=committed$/m,
    'transaction receipt is committed');
like($transaction_receipt, qr/^exit_code=0$/m,
    'transaction receipt binds the payload exit');
like($transaction_receipt,
    qr/^bootstrap_dev=[0-9]+\nbootstrap_ino=[1-9][0-9]*\nbootstrap_sha256=[0-9a-f]{64}$/m,
    'transaction receipt binds the bootstrap source identity');
my @helper_rows = ($transaction_receipt =~
    /^helper=[a-z][a-z0-9_]* dev=[0-9]+ ino=[1-9][0-9]* sha256=[0-9a-f]{64}$/mg);
is(scalar(@helper_rows), scalar(@helper_names),
    'transaction receipt binds every retained helper source identity');
my %child_identity;
while ($transaction_receipt =~
        /^child=(output|evidence|home|tmp|cache) dev=([0-9]+) ino=([1-9][0-9]*) content_sha256=[0-9a-f]{64}$/mg) {
    my ($name, $dev, $ino) = ($1, $2, $3);
    my @actual = stat($target->{$name});
    $child_identity{$name} = "$dev:$ino"
        if @actual && $actual[0] == $dev && $actual[1] == $ino;
}
my %distinct_child = map { $child_identity{$_} => 1 } keys %child_identity;
my @stage_identity = stat($target->{transaction});
is(scalar(keys(%child_identity)) == 5 &&
        scalar(keys(%distinct_child)) == 5 && @stage_identity &&
        !exists($distinct_child{"$stage_identity[0]:$stage_identity[1]"}), 1,
    'transaction receipt identities equal all five distinct children and exclude the stage root');
like($transaction_receipt, qr/^outcome=evidence\/result\.env$/m,
    'transaction receipt uses only its internal outcome path');
like($transaction_receipt, qr/^outcome_sha256=[0-9a-f]{64}$/m,
    'transaction receipt binds the internal outcome content');
open(my $result, '<', "$target->{evidence}/result.env") or die $!;
my $receipt = do { local $/; <$result> }; close($result);
like($receipt, qr/^memory_max_bytes=53687091200$/m, 'memory authority is exact');
like($receipt, qr/^compiler_wall_ms=500$/m, 'compiler deadline is propagated');
like($receipt, qr/^wall_scope=stage2-compiler-native-build-only$/m,
    'deadline scope excludes Stage2 setup and admission');
like($receipt, qr/^runner_zero_proof=not-claimed$/m, 'runner does not claim descendant zero');
for my $payload_file (
        [output => 'payload.out'], [evidence => 'payload.env'],
        [home => 'payload.home'], [tmp => 'payload.tmp'],
        [cache => 'payload.cache']) {
    ok(-f "$target->{$payload_file->[0]}/$payload_file->[1]",
        "payload consumes internal $payload_file->[0] descriptor path");
}

my $collision_base = tempdir(CLEANUP => 1);
($code, $target) = invoke($collision_base, collision => 1);
isnt($code, 0, 'transaction-root collision fails closed');
ok(-d $target->{transaction} &&
        !glob("$collision_base/parents/.stage2.transaction.stage2-runner-txn.*"),
    'collision preserves the existing root and creates no staging residue');

my $preexec_base = tempdir(CLEANUP => 1);
($code, $target) = invoke($preexec_base, dash => '/definitely/absent/dash');
isnt($code, 0, 'pre-exec failure is reported');
ok(!-e $target->{transaction},
    'pre-exec failure removes the complete transaction');
ok(!glob("$preexec_base/parents/.stage2.transaction.stage2-runner-txn.*"),
    'pre-exec failure removes the staging root');

my $wrong_cwd_base = tempdir(CLEANUP => 1);
($code, $target) = invoke($wrong_cwd_base, wrong_cwd => 1);
isnt($code, 0, 'root descriptor must identify the inherited working directory');
ok(!-e $target->{transaction},
    'root/cwd mismatch is rejected before the first filesystem mutation');

($code) = invoke(tempdir(CLEANUP => 1), memory => 1);
isnt($code, 0, 'mismatched memory authority fails closed');
($code) = invoke(tempdir(CLEANUP => 1), bad_fd => 1);
isnt($code, 0, 'missing supervisor-issued lock descriptor fails closed');
($code) = invoke(tempdir(CLEANUP => 1), unlocked => 1);
my $unlocked_rejected = $code != 0;
($code) = invoke(tempdir(CLEANUP => 1), forged_unrelated_lock => 1);
ok($unlocked_rejected && $code != 0,
    'runner rejects free and unrelated-owner lock descriptors without acquisition');
($code) = invoke(tempdir(CLEANUP => 1), legacy_stage2_wall => 1);
isnt($code, 0, 'obsolete whole-Stage2 deadline fails closed');
($code) = invoke(tempdir(CLEANUP => 1), legacy_output => 1);
isnt($code, 0, 'legacy sibling output option is rejected');
($code, $target) = invoke(tempdir(CLEANUP => 1), behavior => 'post-compiler-delay');
is($code, 0, 'runner does not charge non-compiler Stage2 work to compiler wall');
ok(-f "$target->{transaction}/transaction.env",
    'post-compiler work still commits one transaction receipt');
($code) = invoke(tempdir(CLEANUP => 1), mutate_helper_authority => 1);
is($code, 0, 'leaf replacement and ancestor rename cannot redirect retained helpers');

for my $failure (qw(setpgid chdir)) {
    my $base = tempdir(CLEANUP => 1);
    ($code, $target) = invoke($base, child_fail => $failure);
    isnt($code, 0, "$failure failure is reported through the CLOEXEC pipe");
    ok(!-e $target->{transaction} &&
            !glob("$base/parents/.stage2.transaction.stage2-runner-txn.*"),
        "$failure failure leaves no transaction or staging residue");
}

($code, $target) = invoke(tempdir(CLEANUP => 1), behavior => 'payload-failure');
is($code, 17, 'payload failure status is preserved');
ok(-d $target->{transaction}, 'payload failure still publishes one closed transaction');
open(my $failed_txn, '<', "$target->{transaction}/transaction.env") or die $!;
my $failed_receipt = do { local $/; <$failed_txn> }; close($failed_txn);
like($failed_receipt, qr/^status=committed\n.*?^exit_code=17$/ms,
    'failed transaction receipt binds the exact nonzero exit');
open(my $failed_result, '<', "$target->{evidence}/result.env") or die $!;
my $failed_outcome = do { local $/; <$failed_result> }; close($failed_result);
like($failed_outcome, qr/^status=failed\n.*?^exit_code=17$/ms,
    'failed outcome is internal and agrees with the transaction receipt');

done_testing();
