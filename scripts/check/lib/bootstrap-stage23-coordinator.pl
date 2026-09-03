#!/usr/bin/env perl
use strict;
use warnings;
use Cwd qw(realpath);
use Digest::SHA qw(sha256_hex);
use Errno qw(EEXIST ENOENT);
use Fcntl qw(:DEFAULT O_DIRECTORY O_NOFOLLOW FD_CLOEXEC F_GETFD F_SETFD);
use File::Basename qw(dirname basename);
use File::Path qw(remove_tree);
use Getopt::Long qw(GetOptions);
use POSIX ();

require 'syscall.ph';
my $O_CLOEXEC = 02000000;
my %o;
my @role;
GetOptions(
    'mode=s' => \$o{mode}, 'root=s' => \$o{root},
    'transaction-root=s' => \$o{transaction_root},
    'architecture=s' => \$o{architecture}, 'run-id=s' => \$o{run_id},
    'reason=s' => \$o{reason}, 'stage2-bootstrap=s' => \$o{stage2_bootstrap},
    'resume-stage2-transaction=s' => \$o{resume_stage2},
    'heavy-lock=s' => \$o{heavy_lock}, 'owner-journal=s' => \$o{owner_journal},
    'quarantine=s' => \$o{quarantine}, 'systemd-run=s' => \$o{systemd_run},
    'systemctl=s' => \$o{systemctl}, 'cgroup-root=s' => \$o{cgroup_root},
    'role=s@' => \@role, 'allow-test-hooks!' => \$o{allow_test_hooks},
) or die "stage23 coordinator: invalid options\n";

my @required_roles = qw(perl dash env unit_supervisor unit_gate stage2_runner
    session planner_admission cache_policy jobs_policy provenance_facade
    provenance_authority provenance_command provenance_sanity
    provenance_manifest_write provenance_manifest_verify provenance_self_test
    portable_lock_atomic portable_process_lock authority_wiring
    stage4_provenance resume_stage4 progress_watch platform_detect
    candidate_frontend preserve_phase stage2_receiver stage_log
    compiler_deadline planner_producer planner_verifier planner_source
    shared_runner preexec_gate runner_adapter sampler analyzer bootstrap_script
    provenance_verifier facade session_helper
    candidate_builder);
my %allowed_role = map { $_ => 1 } @required_roles;
my %executable = map { $_ => 1 } grep { $_ ne 'planner_source' } @required_roles;
my (%role_path, %role_fh, %role_id);
my ($stage2_bootstrap_fh, $stage2_bootstrap_id);
my ($parent_fh, $stage_fh, $stage_path, $stage_leaf, $destination_leaf);
my ($stage2_authority_fh, $stage2_authority_path);
my $published = 0;

sub fail { die "stage23 coordinator: $_[0]\n" }
sub canonical_absolute {
    my ($path, $name) = @_;
    defined($path) && $path =~ m{\A/} && $path ne '/' &&
        $path !~ m{//|/\.(?:/|\z)|/\.\.(?:/|\z)|/\z}
        or fail("non-canonical $name");
}
sub set_cloexec {
    my ($fh) = @_;
    my $flags = fcntl($fh, F_GETFD, 0);
    defined($flags) && fcntl($fh, F_SETFD, $flags | FD_CLOEXEC)
        or fail('cannot set close-on-exec');
}
sub open_dir {
    my ($path, $name) = @_;
    canonical_absolute($path, $name);
    sysopen(my $fh, $path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | $O_CLOEXEC)
        or fail("open $name: $!");
    my @held = stat($fh); my @named = lstat($path);
    @held && @named && -d _ && !-l _ && $held[0] == $named[0] &&
        $held[1] == $named[1] or fail("$name identity changed");
    return $fh;
}
sub hash_fh {
    my ($fh) = @_;
    seek($fh, 0, 0) or fail("seek role: $!");
    my $sha = Digest::SHA->new(256); $sha->addfile($fh);
    seek($fh, 0, 0) or fail("rewind role: $!");
    return $sha->hexdigest;
}
sub open_role {
    my ($name, $path) = @_;
    canonical_absolute($path, "role $name");
    sysopen(my $fh, $path, O_RDONLY | O_NOFOLLOW | $O_CLOEXEC)
        or fail("open role $name: $!");
    my @held = stat($fh); my @named = lstat($path);
    @held && @named && -f _ && !-l _ && $held[0] == $named[0] &&
        $held[1] == $named[1] or fail("role $name identity changed");
    $executable{$name} && !-x $fh and fail("role $name is not executable");
    return ($fh, join(':', $held[0], $held[1], sprintf('%04o', $held[2] & 07777),
        $held[7], hash_fh($fh)));
}
sub procfd { '/proc/' . $$ . '/fd/' . fileno($_[0]) }
sub safe_relative {
    my ($relative, $name) = @_;
    $relative =~ m{\A[A-Za-z0-9._/-]+\z} && $relative !~ m{\A/|//} &&
        $relative !~ m{(?:\A|/)\.\.?(?:/|\z)} or fail("unsafe $name relative path");
}
sub open_beneath {
    my ($root, $relative, $want_dir, $name) = @_;
    safe_relative($relative, $name);
    my @parts = split m{/}, $relative;
    my $leaf = pop @parts;
    my $parent = $root;
    my @parents;
    for my $part (@parts) {
        sysopen(my $next, procfd($parent) . "/$part",
            O_RDONLY | O_DIRECTORY | O_NOFOLLOW | $O_CLOEXEC)
            or fail("open $name component: $!");
        push @parents, $next; $parent = $next;
    }
    my $flags = O_RDONLY | O_NOFOLLOW | $O_CLOEXEC;
    $flags |= O_DIRECTORY if $want_dir;
    sysopen(my $result, procfd($parent) . "/$leaf", $flags)
        or fail("open $name: $!");
    my @st = stat($result);
    @st && ($want_dir ? -d _ : -f _) or fail("invalid $name type");
    return $result;
}
sub write_exclusive {
    my ($path, $bytes, $mode) = @_;
    sysopen(my $fh, $path, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | $O_CLOEXEC,
        $mode) or fail("publish $path: $!");
    print {$fh} $bytes or fail("write $path: $!");
    $fh->sync or fail("fsync $path: $!");
    close($fh) or fail("close $path: $!");
}
sub hash_file {
    my ($path) = @_;
    sysopen(my $fh, $path, O_RDONLY | O_NOFOLLOW | $O_CLOEXEC)
        or fail("open result $path: $!");
    my $hash = hash_fh($fh); close($fh) or fail("close result: $!");
    return $hash;
}
sub role_snapshot {
    join('', map { "role=$_ identity=$role_id{$_}\n" } sort keys %role_id);
}
sub revalidate_roles {
    for my $name (keys %role_fh) {
        my @held = stat($role_fh{$name}); my @named = lstat($role_path{$name});
        @held && @named && $held[0] == $named[0] && $held[1] == $named[1] &&
            hash_fh($role_fh{$name}) eq (split(':', $role_id{$name}))[-1]
            or fail("role mutation: $name");
    }
}
sub run_child {
    my ($phase, @args) = @_;
    my $name = $phase eq 'stage2' ? 'stage2_runner' :
        $phase eq 'planner' ? 'planner_producer' : 'runner_adapter';
    if (!$o{allow_test_hooks}) {
        $phase eq 'stage2' or fail("real $phase boundary is not integrated");
        my @command = (
            procfd($role_fh{unit_supervisor}), '--phase=stage2',
            "--root=$o{root}", "--evidence-dir=$stage_path/units/stage2/evidence",
            "--run-id=$o{run_id}", "--architecture=$o{architecture}",
            '--memory-max=53687091200', "--heavy-lock=$o{heavy_lock}",
            "--owner-journal=$o{owner_journal}.stage2",
            "--quarantine=$o{quarantine}", "--systemd-run=$o{systemd_run}",
            "--systemctl=$o{systemctl}", "--cgroup-root=$o{cgroup_root}",
            "--env=HOME=$stage_path/units/stage2/home",
            "--env=TMPDIR=$stage_path/units/stage2/tmp",
            '--env=PATH=/usr/bin:/bin', '--env=LC_ALL=C', '--env=LANG=C',
            '--role=env=' . procfd($role_fh{env}),
            '--role=gate_interpreter=' . procfd($role_fh{dash}),
            '--role=gate_helper=' . procfd($role_fh{unit_gate}),
            '--role=payload=' . procfd($role_fh{perl}),
            '--role=stage2_runner=' . procfd($role_fh{stage2_runner}),
            '--role=stage2_bootstrap=' . procfd($stage2_bootstrap_fh),
            '--arg={role:payload}', '--arg={role:stage2_runner}',
            "--arg=--root=$o{root}", "--arg=--transaction-root=$stage_path/stage2",
            '--arg=--bootstrap={role:stage2_bootstrap}',
            "--arg=--outer-lock-path=$o{heavy_lock}",
            '--arg=--compiler-wall-ms=3600000', '--arg=--memory-max=53687091200',
            '--arg=--dash={role:dash}',
        );
        push @command, '--role=dash=' . procfd($role_fh{dash});
        system(@command);
        my $rc = $? & 127 ? 128 + ($? & 127) : $? >> 8;
        $rc == 0 or fail("Stage2 supervisor failed with status $rc");
        -f "$stage_path/stage2/transaction.env" &&
            -f "$stage_path/units/stage2/evidence/terminal.env" &&
            -f "$stage_path/units/stage2/evidence/.terminal.env.commit.$o{run_id}"
            or fail('Stage2 durable result set is incomplete');
        return;
    }
    my $pid = fork(); defined($pid) or fail("fork $phase: $!");
    if ($pid == 0) {
        for my $n (keys %role_fh) { set_cloexec($role_fh{$n}); }
        exec {$role_path{$name}} $role_path{$name}, "--coordinator-phase=$phase", @args;
        POSIX::_exit(126);
    }
    waitpid($pid, 0) == $pid or fail("wait $phase: $!");
    my $rc = $? & 127 ? 128 + ($? & 127) : $? >> 8;
    $rc == 0 or fail("$phase failed with status $rc");
}
sub parse_exact_receipt {
    my ($path, $schema, @keys) = @_;
    sysopen(my $fh, $path, O_RDONLY | O_NOFOLLOW | $O_CLOEXEC)
        or fail("missing receipt $path");
    my %row; while (my $line = <$fh>) {
        chomp $line; $line =~ /\A([a-z][a-z0-9_]*)=(.*)\z/
            or fail("malformed receipt $path");
        !exists($row{$1}) or fail("duplicate receipt key $1"); $row{$1} = $2;
    }
    close($fh) or fail("close receipt $path: $!");
    join(',', sort keys %row) eq join(',', sort @keys)
        or fail("receipt key mismatch $path");
    $row{schema} eq $schema && $row{status} eq 'pass'
        or fail("receipt not PASS $path");
    return \%row;
}
sub parse_single_rows {
    my ($path) = @_;
    sysopen(my $fh, $path, O_RDONLY | O_NOFOLLOW | $O_CLOEXEC)
        or fail("missing receipt $path");
    my %row;
    while (my $line = <$fh>) {
        chomp $line;
        next if $line =~ /\A(?:helper|child)=/;
        $line =~ /\A([a-z][a-z0-9_]*)=(.*)\z/
            or fail("malformed receipt $path");
        !exists($row{$1}) or fail("duplicate receipt key $1");
        $row{$1} = $2;
    }
    close($fh) or fail("close receipt $path: $!");
    return \%row;
}
sub validate_real_stage2 {
    my $transaction = "$stage2_authority_path/transaction.env";
    my $terminal = "$stage_path/units/stage2/evidence/terminal.env";
    my $commit = "$stage_path/units/stage2/evidence/.terminal.env.commit.$o{run_id}";
    my $tx = parse_single_rows($transaction);
    $tx->{schema} eq 'simple-bootstrap-stage2-transaction-v1' &&
        $tx->{status} eq 'committed' && $tx->{exit_code} eq '0'
        or fail('Stage2 transaction is not admitted');
    my $term = parse_single_rows($terminal);
    $term->{schema} eq 'simple-stage3-unit-terminal-v2' &&
        $term->{status} eq 'pass' && $term->{phase} eq 'stage2' &&
        $term->{run_id} eq $o{run_id} &&
        $term->{architecture} eq $o{architecture} &&
        $term->{active_state} eq 'inactive' && $term->{populated} eq '0' &&
        $term->{cleanup} eq 'inactive-populated-zero' &&
        $term->{memory_max_delta} eq '0' && $term->{memory_oom_delta} eq '0' &&
        $term->{memory_oom_kill_delta} eq '0' &&
        $term->{memory_oom_group_kill_delta} eq '0'
        or fail('Stage2 terminal authority mismatch');
    my $prepared = parse_single_rows($commit);
    my @terminal_identity = lstat($terminal);
    $prepared->{schema} eq 'simple-stage3-unit-terminal-commit-v1' &&
        $prepared->{status} eq 'prepared' && $prepared->{phase} eq 'stage2' &&
        $prepared->{run_id} eq $o{run_id} &&
        $prepared->{terminal_sha256} eq hash_file($terminal) &&
        $prepared->{terminal_dev} eq "$terminal_identity[0]" &&
        $prepared->{terminal_ino} eq "$terminal_identity[1]"
        or fail('Stage2 terminal commit mismatch');
    return { artifact_sha256 => hash_file($transaction), terminal_sha256 => hash_file($terminal) };
}
sub bind_resumed_stage2 {
    canonical_absolute($o{resume_stage2}, 'resume Stage2 transaction');
    $stage2_authority_path = $o{resume_stage2};
    $stage2_authority_fh = open_dir($stage2_authority_path,
        'resumed Stage2 transaction');
    my $transaction = "$stage2_authority_path/transaction.env";
    my $tx = parse_single_rows($transaction);
    $tx->{schema} eq 'simple-bootstrap-stage2-transaction-v1' &&
        $tx->{status} eq 'committed' && $tx->{exit_code} eq '0'
        or fail('resumed Stage2 transaction is not committed');
    basename($stage2_authority_path) eq 'stage2'
        or fail('resumed Stage2 transaction has non-canonical layout');
    my $published_root_path = dirname($stage2_authority_path);
    my $published_root = open_dir($published_root_path,
        'resumed Stage23 transaction root');
    my $terminal = open_beneath($published_root,
        'units/stage2/evidence/terminal.env', 0, 'resumed Stage2 terminal');
    my $term = parse_single_rows(procfd($terminal));
    $term->{schema} eq 'simple-stage3-unit-terminal-v2' &&
        $term->{status} eq 'pass' && $term->{phase} eq 'stage2' &&
        $term->{architecture} eq $o{architecture} &&
        $term->{run_id} =~ /\A[A-Za-z0-9_-]{8,64}\z/ &&
        $term->{active_state} eq 'inactive' && $term->{populated} eq '0' &&
        $term->{cleanup} eq 'inactive-populated-zero' &&
        $term->{memory_max_delta} eq '0' && $term->{memory_oom_delta} eq '0' &&
        $term->{memory_oom_kill_delta} eq '0' &&
        $term->{memory_oom_group_kill_delta} eq '0' &&
        $term->{memory_swap_current_terminal_bytes} eq '0'
        or fail('resumed Stage2 terminal authority mismatch');
    safe_relative("units/stage2/evidence/.terminal.env.commit.$term->{run_id}",
        'resumed Stage2 terminal commit');
    my $commit = open_beneath($published_root,
        "units/stage2/evidence/.terminal.env.commit.$term->{run_id}", 0,
        'resumed Stage2 terminal commit');
    my $prepared = parse_single_rows(procfd($commit));
    my @terminal_identity = stat($terminal);
    $prepared->{schema} eq 'simple-stage3-unit-terminal-commit-v1' &&
        $prepared->{status} eq 'prepared' && $prepared->{phase} eq 'stage2' &&
        $prepared->{run_id} eq $term->{run_id} &&
        $prepared->{architecture} eq $o{architecture} &&
        $prepared->{unit} eq $term->{unit} &&
        $prepared->{terminal_sha256} eq hash_fh($terminal) &&
        $prepared->{terminal_dev} eq "$terminal_identity[0]" &&
        $prepared->{terminal_ino} eq "$terminal_identity[1]"
        or fail('resumed Stage2 terminal commit mismatch');
    my $base = "output/stage3/$o{architecture}";
    my %bound_relative = (
        parent => 'output/stage2/' . $o{architecture} .
            '/stage2-provenance.receipt',
        source => "$base/source-inputs-before.txt",
        git => "$base/git-state-before.env",
        runtime => "$base/runtime-admitted.txt",
        tool => "$base/tool-authority-before.txt",
    );
    my (%bound_fh, %bound_sha);
    for my $name (sort keys %bound_relative) {
        $bound_fh{$name} = open_beneath($stage2_authority_fh,
            $bound_relative{$name}, 0, "resumed Stage2 $name authority");
        $bound_sha{$name} = hash_fh($bound_fh{$name});
    }
    my @st = stat($stage2_authority_fh);
    my $freeze_sha = hash_file("$stage_path/freeze/source.snapshot");
    my $binding = join('',
        "schema=simple-stage23-resume-binding-v1\n", "status=bound\n",
        "run_id=$o{run_id}\n", "architecture=$o{architecture}\n",
        "stage2_run_id=$term->{run_id}\n",
        "stage2_display=$stage2_authority_path\n",
        "stage2_dev=$st[0]\n", "stage2_ino=$st[1]\n",
        "transaction_sha256=" . hash_file($transaction) . "\n",
        "terminal_sha256=" . hash_fh($terminal) . "\n",
        "terminal_commit_sha256=" . hash_fh($commit) . "\n",
        "parent_v1_sha256=$bound_sha{parent}\n",
        "source_snapshot_sha256=$bound_sha{source}\n",
        "git_receipt_sha256=$bound_sha{git}\n",
        "runtime_snapshot_sha256=$bound_sha{runtime}\n",
        "tool_snapshot_sha256=$bound_sha{tool}\n",
        "source_freeze_sha256=$freeze_sha\n");
    write_exclusive("$stage_path/resume-binding.env", $binding, 0600);
    for my $name (keys %bound_fh) {
        close($bound_fh{$name}) or fail("close resumed Stage2 $name: $!");
    }
    close($commit) or fail("close resumed Stage2 terminal commit: $!");
    close($terminal) or fail("close resumed Stage2 terminal: $!");
    close($published_root) or fail("close resumed Stage23 transaction root: $!");
    return { artifact_sha256 => hash_file($transaction),
        terminal_sha256 => $prepared->{terminal_sha256} };
}
sub run_real_planner {
    my $stage2_root = $stage2_authority_fh;
    my $planner_root = open_dir("$stage_path/planner", 'planner capsule');
    my $stage2_base = "output/stage2/$o{architecture}";
    my $evidence_base = "output/stage3/$o{architecture}";
    my %relative = (
        compiler => "$stage2_base/simple",
        sanity => "$stage2_base/stage2-sanity.receipt",
        provenance => "$stage2_base/stage2-provenance.receipt",
        runtime => "$evidence_base/stage2-runtime-authority",
        git => "$evidence_base/git-state-before.env",
    );
    my $compiler = open_beneath($stage2_root, $relative{compiler}, 0,
        'admitted Stage2 compiler');
    -x $compiler or fail('admitted Stage2 compiler is not executable');
    my $sanity = open_beneath($stage2_root, $relative{sanity}, 0,
        'Stage2 sanity');
    my $provenance = open_beneath($stage2_root, $relative{provenance}, 0,
        'Stage2 provenance');
    my $runtime = open_beneath($stage2_root, $relative{runtime}, 1,
        'Stage2 runtime');
    my $git = open_beneath($stage2_root, $relative{git}, 0,
        'Stage2 Git state');
    my $producer = procfd($role_fh{planner_producer});
    my @command = ($producer,
        '--capsule-root=' . procfd($planner_root),
        '--verifier-descriptor=' . procfd($role_fh{planner_verifier}),
        "--root=$o{root}", '--target=//bootstrap:stage3', "--reason=$o{reason}",
        '--stage2-transaction-descriptor=' . procfd($stage2_root),
        "--stage2-transaction-display=$stage2_authority_path",
        '--parent-compiler-transaction-relative=' . $relative{compiler},
        '--parent-compiler-descriptor=' . procfd($compiler),
        "--parent-compiler-display=$stage2_authority_path/$relative{compiler}",
        '--parent-sanity-transaction-relative=' . $relative{sanity},
        '--parent-sanity-descriptor=' . procfd($sanity),
        "--parent-sanity-display=$stage2_authority_path/$relative{sanity}",
        '--parent-provenance-transaction-relative=' . $relative{provenance},
        '--parent-provenance-descriptor=' . procfd($provenance),
        "--parent-provenance-display=$stage2_authority_path/$relative{provenance}",
        '--runtime-dir-descriptor=' . procfd($runtime),
        "--runtime-dir-display=$stage2_authority_path/$relative{runtime}",
        '--planner-source-descriptor=' . procfd($role_fh{planner_source}),
        "--planner-source-display=$o{root}/src/app/cli/bootstrap_reason_planner.spl",
        '--git-state-descriptor=' . procfd($git),
        "--git-state-display=$stage2_authority_path/$relative{git}",
        "--out=$stage_path/planner/planner-admission-v2.env");
    system(@command);
    my $rc = $? & 127 ? 128 + ($? & 127) : $? >> 8;
    $rc == 0 or fail("planner producer failed with status $rc");
    my $receipt = "$stage_path/planner/planner-admission-v2.env";
    -f $receipt or fail('planner receipt absent');
    my @verify = (procfd($role_fh{dash}), '-c',
        '. "$1"; bootstrap_planner_v2_verify "$2" "$3" "$4"',
        'stage23-planner-verify', procfd($role_fh{planner_verifier}),
        $receipt, $o{root}, procfd($planner_root));
    system(@verify);
    $rc = $? & 127 ? 128 + ($? & 127) : $? >> 8;
    $rc == 0 or fail("planner verifier failed with status $rc");
    my $planner_binary = open_beneath($planner_root, 'planner', 0,
        'fresh planner executable');
    -x $planner_binary or fail('fresh planner is not executable');
    my $planner_receipt = open_beneath($planner_root,
        'planner-admission-v2.env', 0, 'planner admission receipt');
    return { receipt_sha256 => hash_file($receipt), path => $receipt,
        compiler => $compiler, runtime => $runtime, git => $git,
        planner_binary => $planner_binary, planner_receipt => $planner_receipt,
        stage2_root => $stage2_root, planner_root => $planner_root };
}
sub receipt_value {
    my ($path, $key) = @_;
    my $rows = parse_single_rows($path);
    exists($rows->{$key}) or fail("missing $key in $path");
    return $rows->{$key};
}
sub prepare_parent_provenance {
    my ($planner) = @_;
    my $root = $planner->{stage2_root};
    my $base = "output/stage3/$o{architecture}";
    my %relative = (
        candidate => "$base/stage2-admitted/simple",
        admission => "$base/stage2-admitted/admission.env",
        source => "$base/source-inputs-before.txt",
        runtime => "$base/runtime-admitted.txt",
        tool => "$base/tool-authority-before.txt",
        git => "$base/git-state-before.env",
        sanity => "$base/stage2-sanity.env",
        receiver => "$base/stage2-receiver.env",
        lineage => "output/stage2/$o{architecture}/stage2-provenance.receipt",
    );
    my %fh;
    for my $name (keys %relative) {
        $fh{$name} = open_beneath($root, $relative{$name}, 0,
            "Stage2 parent $name");
    }
    -x $fh{candidate} or fail('Stage2 admitted candidate is not executable');
    my $args_sha = receipt_value(procfd($fh{admission}), 'build_args_sha256');
    $args_sha =~ /\A[0-9a-f]{64}\z/ or fail('invalid Stage2 build argv hash');
    my @verify = (procfd($role_fh{dash}), '-c',
        '. "$1"; bootstrap_stage3_verify_stage2_admission_receipt "$2" "$3" "$4" "$5" "$6" "$7" "$8" "$9" "${10}" "${11}" "${12}" "${13}" "${14}" "${15}"',
        'stage23-parent-admission', procfd($role_fh{provenance_sanity}),
        procfd($fh{admission}), procfd($fh{candidate}), procfd($fh{source}),
        procfd($fh{runtime}), procfd($fh{tool}), $args_sha,
        procfd($fh{sanity}), procfd($fh{receiver}),
        "$stage2_authority_path/$relative{candidate}",
        "$stage2_authority_path/$relative{source}",
        "$stage2_authority_path/$relative{runtime}",
        "$stage2_authority_path/$relative{tool}",
        "$stage2_authority_path/$relative{sanity}",
        "$stage2_authority_path/$relative{receiver}");
    system(@verify);
    my $rc = $? & 127 ? 128 + ($? & 127) : $? >> 8;
    $rc == 0 or fail("Stage2 parent admission verification failed with status $rc");
    mkdir("$stage_path/stage3/parent", 0700)
        or fail("create parent provenance directory: $!");
    my $manifest_path = procfd($fh{lineage});
    seek($fh{lineage}, 0, 0) or fail("seek Stage2 parent-v1: $!");
    my %parent_v1;
    while (my $line = readline($fh{lineage})) {
        chomp($line);
        $line =~ /\A([a-z][a-z0-9_-]*)=(.*)\z/
            or fail('malformed Stage2 parent-v1 receipt');
        !exists($parent_v1{$1}) or fail("duplicate Stage2 parent-v1 key $1");
        $parent_v1{$1} = $2;
    }
    seek($fh{lineage}, 0, 0) or fail("rewind Stage2 parent-v1: $!");
    join(',', sort keys %parent_v1) eq join(',', sort qw(schema stage2-provenance
            authority candidate_sha256 source_snapshot_sha256
            runtime_snapshot_sha256 tool_authority_sha256
            admission_receipt_sha256)) &&
        $parent_v1{schema} eq 'simple-bootstrap-stage2-parent-provenance-v1' &&
        $parent_v1{'stage2-provenance'} eq 'pure-simple' &&
        ($parent_v1{authority} eq 'explicit-full-bootstrap-stage2-trust-root' ||
         $parent_v1{authority} eq 'admitted-pure-simple-runtime-stage2-trust-root') &&
        $parent_v1{candidate_sha256} eq hash_fh($fh{candidate}) &&
        $parent_v1{source_snapshot_sha256} eq hash_fh($fh{source}) &&
        $parent_v1{runtime_snapshot_sha256} eq hash_fh($fh{runtime}) &&
        $parent_v1{tool_authority_sha256} eq hash_fh($fh{tool}) &&
        $parent_v1{admission_receipt_sha256} eq hash_fh($fh{admission})
        or fail('Stage2 parent-v1 authentication mismatch');
    my $receipt_path = "$stage_path/stage3/parent/parent-v1-authentication.env";
    my $receipt = join('',
        "schema=simple-stage23-parent-v1-authentication-v1\n",
        "status=pass\n", "run_id=$o{run_id}\n",
        "architecture=$o{architecture}\n",
        "parent_v1_sha256=" . hash_fh($fh{lineage}) . "\n",
        "candidate_sha256=" . hash_fh($fh{candidate}) . "\n",
        "source_snapshot_sha256=" . hash_fh($fh{source}) . "\n",
        "runtime_snapshot_sha256=" . hash_fh($fh{runtime}) . "\n",
        "tool_snapshot_sha256=" . hash_fh($fh{tool}) . "\n",
        "git_receipt_sha256=" . hash_fh($fh{git}) . "\n",
        "stage2_admission_sha256=" . hash_fh($fh{admission}) . "\n");
    write_exclusive($receipt_path, $receipt, 0600);
    return { manifest => $manifest_path, verification => $receipt_path,
        %fh, relative => \%relative };
}
sub run_real_stage3 {
    my ($planner, $parent) = @_;
    my $unit = "$stage_path/units/stage3";
    my $evidence = "$unit/evidence";
    my $out = "$stage_path/stage3";
    mkdir("$out/cache", 0700) or fail("create Stage3 cache: $!");
    my %path = (
        compatibility => "$out/compatibility",
        raw => "$out/rss.raw", memory => "$out/memory.ndjson",
        phase => "$out/phase.ndjson", descriptor => "$out/descriptor.env",
        candidate => "$out/simple", provenance => "$out/provenance.env",
        progress => "$out/progress.events",
    );
    my %run_env = (
        BSTAGE3_RUN_ROOT => $o{root}, BSTAGE3_RUN_EVIDENCE => $evidence,
        BSTAGE3_RUN_ID => $o{run_id}, BSTAGE3_RUN_ARCHITECTURE => $o{architecture},
        BSTAGE3_RUN_HEAVY_LOCK => $o{heavy_lock},
        BSTAGE3_RUN_OWNER_JOURNAL => "$o{owner_journal}.stage3",
        BSTAGE3_RUN_QUARANTINE => $o{quarantine},
        BSTAGE3_RUN_SYSTEMD_RUN => $o{systemd_run},
        BSTAGE3_RUN_SYSTEMCTL => $o{systemctl},
        BSTAGE3_RUN_CGROUP_ROOT => $o{cgroup_root},
        BSTAGE3_RUN_HOME => "$unit/home", BSTAGE3_RUN_TMPDIR => "$unit/tmp",
        BSTAGE3_RUN_PATH => '/usr/bin:/bin',
        BSTAGE3_RUN_SOURCE_OUTPUT => $stage2_authority_path,
        BSTAGE3_RUN_STAGE2_TRANSACTION_ROOT => procfd($planner->{stage2_root}),
        BSTAGE3_RUN_COMPATIBILITY_MARKER => $path{compatibility},
        BSTAGE3_RUN_RAW => $path{raw}, BSTAGE3_RUN_MEMORY => $path{memory},
        BSTAGE3_RUN_PHASE => $path{phase}, BSTAGE3_RUN_DESCRIPTOR => $path{descriptor},
        BSTAGE3_RUN_PARENT_PROVENANCE => $parent->{manifest},
        BSTAGE3_RUN_PARENT_PROVENANCE_VERIFY => $parent->{verification},
        BSTAGE3_RUN_SOURCE_SNAPSHOT => procfd($parent->{source}),
        BSTAGE3_RUN_GIT_RECEIPT => procfd($parent->{git}),
        BSTAGE3_RUN_RUNTIME_SNAPSHOT => procfd($parent->{runtime}),
        BSTAGE3_RUN_TOOL_SNAPSHOT => procfd($parent->{tool}),
        BSTAGE3_RUN_STAGE2_ADMISSION => procfd($parent->{admission}),
        BSTAGE3_RUN_PLANNER_RECEIPT => procfd($planner->{planner_receipt}),
        BSTAGE3_RUN_CACHE => "$out/cache",
        BSTAGE3_RUN_RUNTIME => procfd($planner->{runtime}),
        BSTAGE3_RUN_CANDIDATE => $path{candidate},
        BSTAGE3_RUN_CANDIDATE_PROVENANCE => $path{provenance},
        BSTAGE3_RUN_PROGRESS => $path{progress},
        BSTAGE3_RUN_SUPERVISOR => procfd($role_fh{unit_supervisor}),
        BSTAGE3_RUN_GATE => procfd($role_fh{unit_gate}),
        BSTAGE3_RUN_RUNNER => procfd($role_fh{shared_runner}),
        BSTAGE3_RUN_SAMPLER => procfd($role_fh{sampler}),
        BSTAGE3_RUN_ANALYZER => procfd($role_fh{analyzer}),
        BSTAGE3_RUN_ADMITTED_COMPILER => procfd($parent->{candidate}),
        BSTAGE3_RUN_DASH => procfd($role_fh{dash}),
        BSTAGE3_RUN_PERL => procfd($role_fh{perl}),
        BSTAGE3_RUN_ENV_TOOL => procfd($role_fh{env}),
        BSTAGE3_RUN_SESSION_HELPER => procfd($role_fh{session_helper}),
        BSTAGE3_RUN_BOOTSTRAP_SCRIPT => procfd($role_fh{bootstrap_script}),
        BSTAGE3_RUN_CANDIDATE_BUILDER => procfd($role_fh{candidate_builder}),
        BSTAGE3_RUN_PLANNER => procfd($planner->{planner_binary}),
        BSTAGE3_RUN_PROVENANCE_VERIFIER => procfd($role_fh{provenance_verifier}),
        BSTAGE3_RUN_FACADE => procfd($role_fh{provenance_facade}),
        BSTAGE3_RUN_SAMPLER_SHA256 => hash_fh($role_fh{sampler}),
        BSTAGE3_RUN_ANALYZER_SHA256 => hash_fh($role_fh{analyzer}),
        BSTAGE3_RUN_ADMITTED_COMPILER_SHA256 => hash_fh($parent->{candidate}),
        BSTAGE3_RUN_DASH_SHA256 => hash_fh($role_fh{dash}),
        BSTAGE3_RUN_CANDIDATE_BUILDER_SHA256 => hash_fh($role_fh{candidate_builder}),
        BSTAGE3_RUN_RUNNER_SHA256 => hash_fh($role_fh{shared_runner}),
        BSTAGE3_RUN_PROVENANCE_VERIFIER_SHA256 => hash_fh($role_fh{provenance_verifier}),
    );
    local %ENV = (%run_env, SIMPLE_EVIDENCE_RUN_ID => $o{run_id},
        LC_ALL => 'C', LANG => 'C', PATH => '/usr/bin:/bin');
    system(procfd($role_fh{dash}), '-c',
        '. "$1"; bootstrap_stage3_run_evidenced', 'stage23-stage3',
        procfd($role_fh{runner_adapter}));
    my $rc = $? & 127 ? 128 + ($? & 127) : $? >> 8;
    $rc == 0 or fail("Stage3 supervisor/runner failed with status $rc");
    my $terminal = "$evidence/terminal.env";
    my $terminal_commit = "$evidence/.terminal.env.commit.$o{run_id}";
    my $runner = "$evidence/runner-receipt.env";
    my $runner_commit = "$evidence/.runner-receipt.commit.$o{run_id}";
    for my $required ($terminal, $terminal_commit, $runner, $runner_commit,
            $path{candidate}, $path{provenance}) {
        -f $required && !-l $required or fail("missing Stage3 result $required");
    }
    my $term = parse_single_rows($terminal);
    $term->{schema} eq 'simple-stage3-unit-terminal-v2' &&
        $term->{status} eq 'pass' && $term->{phase} eq 'stage3' &&
        $term->{run_id} eq $o{run_id} && $term->{architecture} eq $o{architecture} &&
        $term->{active_state} eq 'inactive' && $term->{populated} eq '0' &&
        $term->{memory_max_delta} eq '0' && $term->{memory_oom_delta} eq '0' &&
        $term->{memory_oom_kill_delta} eq '0' &&
        $term->{memory_oom_group_kill_delta} eq '0'
        or fail('Stage3 terminal authority mismatch');
    my $component = parse_single_rows($runner);
    $component->{schema} eq 'simple-stage3-shared-runner-receipt-v1' &&
        $component->{status} eq 'component-pass' && $component->{authority} eq 'false' &&
        $component->{transaction_admission} eq 'false' &&
        $component->{run_id} eq $o{run_id} &&
        $component->{architecture} eq $o{architecture} &&
        $component->{cleanup} eq 'measured-subtree-zero-analyzer-complete'
        or fail('Stage3 component receipt mismatch');
    return { terminal_sha256 => hash_file($terminal),
        runner_sha256 => hash_file($runner),
        provenance_sha256 => hash_file($path{provenance}),
        candidate_sha256 => hash_file($path{candidate}), terminal => $terminal,
        runner => $runner };
}
sub cleanup_stage {
    return if $published || !defined($stage_path) || !-e $stage_path;
    my $errors; remove_tree($stage_path, { error => \$errors });
    $errors //= [];
    @$errors and fail('rollback cleanup failed');
}
$SIG{INT} = $SIG{TERM} = $SIG{HUP} = sub { fail('interrupted') };

for my $key (qw(mode root transaction_root architecture run_id reason heavy_lock
        owner_journal quarantine systemd_run systemctl cgroup_root)) {
    defined($o{$key}) && length($o{$key}) or fail("missing --$key");
}
$o{mode} =~ /\A(?:fresh|resume)\z/ or fail('invalid mode');
$o{architecture} eq 'x86_64-unknown-linux-gnu' or fail('unsupported architecture');
$o{run_id} =~ /\A[A-Za-z0-9_-]{8,64}\z/ or fail('invalid run id');
$o{reason} =~ /\A\/\/bootstrap:stage3:[A-Za-z0-9_.-]{1,96}\z/
    or fail('invalid typed reason');
canonical_absolute($o{root}, 'root');
(realpath($o{root}) // '') eq $o{root} or fail('root is not physical');
canonical_absolute($o{transaction_root}, 'transaction root');
!(-e $o{transaction_root} || -l $o{transaction_root}) or fail('transaction collision');
if ($o{mode} eq 'fresh') {
    defined($o{stage2_bootstrap}) && !defined($o{resume_stage2})
        or fail('fresh mode authority mismatch');
} else {
    defined($o{resume_stage2}) && !defined($o{stage2_bootstrap})
        or fail('resume mode authority mismatch');
}
for my $spec (@role) {
    $spec =~ /\A([a-z][a-z0-9_]*)=(\/.*)\z/ or fail('invalid role binding');
    my ($name, $path) = ($1, $2); exists($allowed_role{$name})
        or fail("unknown role $name");
    !exists($role_path{$name}) or fail("duplicate role $name");
    $role_path{$name} = $path;
}
for my $name (@required_roles) { exists($role_path{$name}) or fail("missing role $name"); }
for my $name (@required_roles) {
    ($role_fh{$name}, $role_id{$name}) = open_role($name, $role_path{$name});
}
if ($o{mode} eq 'fresh') {
    ($stage2_bootstrap_fh, $stage2_bootstrap_id) =
        open_role('stage2_bootstrap', $o{stage2_bootstrap});
    -x $stage2_bootstrap_fh or fail('Stage2 bootstrap is not executable');
}
my %seen_exec;
for my $name (grep { $executable{$_} } @required_roles) {
    my ($dev, $ino) = split(':', $role_id{$name});
    !exists($seen_exec{"$dev:$ino"}) or fail("executable role alias: $name");
    $seen_exec{"$dev:$ino"} = $name;
}

my $destination_parent = dirname($o{transaction_root});
$destination_leaf = basename($o{transaction_root});
$parent_fh = open_dir($destination_parent, 'transaction parent');
$stage_leaf = ".$destination_leaf.stage23.$o{run_id}.$$";
syscall(&SYS_mkdirat, fileno($parent_fh), $stage_leaf, 0700) == 0
    or fail("create staging: $!");
$stage_path = "$destination_parent/$stage_leaf";
$stage_fh = open_dir($stage_path, 'staging root');
eval {
    for my $dir (qw(freeze planner stage3 units units/stage2 units/stage2/home units/stage2/tmp units/stage3 units/stage3/home units/stage3/tmp)) {
        mkdir("$stage_path/$dir", 0700) or fail("create $dir: $!");
    }
    my @rst = stat(open_dir($o{root}, 'repository root'));
    my $roles = role_snapshot();
    my $source = "schema=simple-stage23-source-freeze-v1\nroot_dev=$rst[0]\nroot_ino=$rst[1]\nroles_sha256=" . sha256_hex($roles) . "\n";
    write_exclusive("$stage_path/freeze/roles.env", $roles, 0600);
    write_exclusive("$stage_path/freeze/source.snapshot", $source, 0600);
    revalidate_roles();
    if ($o{mode} eq 'fresh') {
        run_child('stage2', "--root=$o{root}", "--transaction-root=$stage_path/stage2",
            "--bootstrap=$o{stage2_bootstrap}", "--jobs=16", '--memory=53687091200');
        $stage2_authority_path = "$stage_path/stage2";
        $stage2_authority_fh = open_dir($stage2_authority_path,
            'fresh Stage2 transaction');
    } elsif ($o{allow_test_hooks}) {
        run_child('stage2', "--resume=$o{resume_stage2}",
            "--transaction-root=$stage_path/stage2");
        $stage2_authority_path = "$stage_path/stage2";
        $stage2_authority_fh = open_dir($stage2_authority_path,
            'test resumed Stage2 transaction');
    }
    my $s2;
    if ($o{allow_test_hooks}) {
        $s2 = parse_exact_receipt("$stage_path/stage2/coordinator-stage2.env",
            'simple-stage23-stage2-boundary-v1', qw(schema status mode run_id architecture artifact_sha256));
        $s2->{mode} eq $o{mode} && $s2->{run_id} eq $o{run_id} &&
            $s2->{architecture} eq $o{architecture} or fail('Stage2 correlation mismatch');
    } elsif ($o{mode} eq 'resume') {
        $s2 = bind_resumed_stage2();
    } else {
        $s2 = validate_real_stage2();
    }
    revalidate_roles();
    my $planner;
    if ($o{allow_test_hooks}) {
        run_child('planner', "--root=$o{root}", "--capsule-root=$stage_path/planner",
            "--target=//bootstrap:stage3", "--reason=$o{reason}");
        $planner = parse_exact_receipt("$stage_path/planner/coordinator-planner.env",
            'simple-stage23-planner-boundary-v1', qw(schema status run_id architecture target reason receipt_sha256));
        $planner->{run_id} eq $o{run_id} && $planner->{architecture} eq $o{architecture} &&
            $planner->{target} eq '//bootstrap:stage3' && $planner->{reason} eq $o{reason}
            or fail('planner correlation mismatch');
    } else {
        $planner = run_real_planner();
    }
    revalidate_roles();
    my $s3;
    if ($o{allow_test_hooks}) {
        run_child('stage3', "--root=$o{root}", "--stage-root=$stage_path/stage3",
            "--unit-root=$stage_path/units/stage3", "--run-id=$o{run_id}",
            "--architecture=$o{architecture}", '--jobs=1', '--memory=8589934592');
        $s3 = parse_exact_receipt("$stage_path/stage3/coordinator-stage3.env",
            'simple-stage23-stage3-boundary-v1', qw(schema status run_id architecture planner_receipt_sha256 terminal_sha256 runner_sha256 provenance_sha256 candidate_sha256 all_units_inactive all_cgroups_empty cleanup_complete));
        $s3->{run_id} eq $o{run_id} && $s3->{architecture} eq $o{architecture} &&
            $s3->{planner_receipt_sha256} eq $planner->{receipt_sha256} &&
            $s3->{all_units_inactive} eq 'true' && $s3->{all_cgroups_empty} eq 'true' &&
            $s3->{cleanup_complete} eq 'true' or fail('Stage3 correlation mismatch');
    } else {
        my $parent = prepare_parent_provenance($planner);
        $s3 = run_real_stage3($planner, $parent);
    }
    revalidate_roles();
    my $coordinator = join('',
        "schema=simple-stage23-transaction-admission-v1\n", "status=pass\n",
        "mode=$o{mode}\n", "run_id=$o{run_id}\n", "architecture=$o{architecture}\n",
        "freeze_sha256=" . sha256_hex($source . $roles) . "\n",
        "stage2_transaction_sha256=$s2->{artifact_sha256}\n",
        "planner_receipt_sha256=$planner->{receipt_sha256}\n",
        "stage3_terminal_sha256=$s3->{terminal_sha256}\n",
        "stage3_runner_sha256=$s3->{runner_sha256}\n",
        "stage3_provenance_sha256=$s3->{provenance_sha256}\n",
        "candidate_sha256=$s3->{candidate_sha256}\n",
        "compatibility_authority=false\n", "all_units_inactive=true\n",
        "all_cgroups_empty=true\n", "cleanup_complete=true\n");
    my $prepared_path = "$stage_path/.coordinator.env.prepared.$o{run_id}";
    my $prepared = join('',
        "schema=simple-stage23-transaction-admission-prepared-v1\n",
        "status=prepared\n", "canonical_status=not-published\n",
        "run_id=$o{run_id}\n", "coordinator_sha256=" . sha256_hex($coordinator) . "\n");
    write_exclusive($prepared_path, $prepared, 0600);
    my @prepared_identity = lstat($prepared_path);
    my $commit = join('',
        "schema=simple-stage23-transaction-admission-commit-v1\n",
        "status=prepared\n", "canonical_status=not-published\n",
        "run_id=$o{run_id}\n", "prepared_dev=$prepared_identity[0]\n",
        "prepared_ino=$prepared_identity[1]\n",
        "prepared_sha256=" . hash_file($prepared_path) . "\n",
        "coordinator_sha256=" . sha256_hex($coordinator) . "\n");
    write_exclusive("$stage_path/.coordinator.env.commit.$o{run_id}", $commit, 0600);
    write_exclusive("$stage_path/coordinator.env", $coordinator, 0600);
    $stage_fh->sync or fail("fsync staging: $!");
    syscall(&SYS_renameat2, fileno($parent_fh), $stage_leaf, fileno($parent_fh),
        $destination_leaf, 1) == 0 or fail("publish transaction: $!");
    $published = 1;
    $parent_fh->sync or fail("fsync transaction parent: $!");
    1;
} or do {
    my $error = $@ || "stage23 coordinator: unknown failure\n";
    eval { cleanup_stage(); 1 } or $error .= $@;
    die $error;
};
print "stage23 coordinator: PASS $o{transaction_root}\n";
