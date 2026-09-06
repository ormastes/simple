#!/usr/bin/env perl
use strict;
use warnings;
use Cwd qw(realpath);
use Digest::SHA qw(sha256_hex);
use Errno qw(EINTR EWOULDBLOCK EAGAIN ENOENT);
use Fcntl qw(:DEFAULT :flock O_NOFOLLOW O_DIRECTORY FD_CLOEXEC F_DUPFD
    F_GETFD F_SETFD);
use File::Basename qw(dirname);
use Getopt::Long qw(GetOptions);
use IO::Handle;
use POSIX qw(dup2 setpgid);

require 'syscall.ph';

my %o = (compiler_wall_ms => 3_600_000, memory_max => 53_687_091_200,
    dash => '/usr/bin/dash');
my @helper;
GetOptions(
    'root=s' => \$o{root}, 'transaction-root=s' => \$o{transaction_root},
    'bootstrap=s' => \$o{bootstrap}, 'memory-max=i' => \$o{memory_max},
    'outer-lock-fd=i' => \$o{outer_lock_fd},
    'outer-lock-path=s' => \$o{outer_lock_path},
    'compiler-wall-ms=i' => \$o{compiler_wall_ms},
    'dash=s' => \$o{dash},
    'helper=s@' => \@helper,
    'stage2-wall-ms=i' => \$o{legacy_wall_ms},
    'allow-test-hooks!' => \$o{allow_test_hooks},
) or die "stage2 runner: invalid options\n";

sub normalized_absolute {
    my ($path, $name) = @_;
    $path =~ m{\A/} && $path ne '/' &&
        $path !~ m{//|/\.(?:/|\z)|/\.\.(?:/|\z)|/\z}
        or die "stage2 runner: non-canonical $name: $path\n";
}
sub preflight_absent {
    my ($path, $name) = @_;
    normalized_absolute($path, $name);
    !(-e $path || -l $path) or die "stage2 runner: $name collision: $path\n";
    my $cursor = dirname($path);
    while (!(-e $cursor || -l $cursor)) {
        my $next = dirname($cursor);
        $next ne $cursor or die "stage2 runner: no existing ancestor for $name\n";
        $cursor = $next;
    }
    -d $cursor && !-l $cursor or die "stage2 runner: invalid ancestor for $name\n";
    (realpath($cursor) // '') eq $cursor
        or die "stage2 runner: aliased ancestor for $name\n";
}
sub sync_directory {
    my ($fh, $name) = @_;
    $fh->sync or die "stage2 runner: fsync $name directory: $!\n";
}
sub renameat_noreplace {
    my ($from_dir, $from, $to_dir, $to, $name) = @_;
    my $RENAME_NOREPLACE = 1;
    syscall(&SYS_renameat2, fileno($from_dir), $from, fileno($to_dir), $to,
        $RENAME_NOREPLACE) == 0
        or die "stage2 runner: publish $name transaction: $!\n";
}
sub open_anchored_parent {
    my ($path, $name) = @_;
    my $parent_path = dirname($path);
    my $leaf = substr($path,
        length($parent_path) + ($parent_path eq '/' ? 0 : 1));
    $leaf ne '' && $leaf !~ m{/}
        or die "stage2 runner: invalid $name leaf\n";
    sysopen(my $parent, $parent_path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW)
        or die "stage2 runner: open $name parent: $!\n";
    set_cloexec($parent, 1);
    my @held = stat($parent); my @path = lstat($parent_path);
    @held && @path && -d _ && !-l _ &&
        $held[0] == $path[0] && $held[1] == $path[1]
        or die "stage2 runner: $name parent identity mismatch\n";
    return ($parent, $leaf);
}
sub mkdirat_private {
    my ($parent, $leaf, $name) = @_;
    syscall(&SYS_mkdirat, fileno($parent), $leaf, 0700) == 0
        or die "stage2 runner: create $name directory: $!\n";
}
sub unlinkat_directory {
    my ($parent, $leaf, $name) = @_;
    my $AT_REMOVEDIR = 0x200;
    syscall(&SYS_unlinkat, fileno($parent), $leaf, $AT_REMOVEDIR) == 0
        or die "stage2 runner: remove $name directory: $!\n";
}
sub unlinkat_directory_cleanup {
    my ($parent, $leaf, $name) = @_;
    my $AT_REMOVEDIR = 0x200;
    return if syscall(&SYS_unlinkat, fileno($parent), $leaf, $AT_REMOVEDIR) == 0;
    return if $! == ENOENT;
    die "stage2 runner: remove $name directory: $!\n";
}
sub open_child_directory {
    my ($parent, $leaf, $name) = @_;
    my $path = '/proc/self/fd/' . fileno($parent) . "/$leaf";
    sysopen(my $fh, $path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW)
        or die "stage2 runner: open $name directory: $!\n";
    set_cloexec($fh, 1);
    return $fh;
}
my @transaction_children = qw(output evidence home tmp cache);

sub create_transaction {
    my ($root) = @_;
    my ($parent, $leaf) = open_anchored_parent($root, 'transaction root');
    my $staging = ".$leaf.stage2-runner-txn.$$";
    mkdirat_private($parent, $staging, 'transaction root');
    my $stage = open_child_directory($parent, $staging, 'transaction root');
    my %child;
    my @created;
    eval {
        for my $name (@transaction_children) {
            mkdirat_private($stage, $name, "transaction child $name");
            push @created, $name;
            $child{$name} = open_child_directory(
                $stage, $name, "transaction child $name");
        }
        sync_directory($stage, 'staged transaction root');
        1;
    } or do {
        my $error = $@ || "stage2 runner: create transaction failed\n";
        my @cleanup_errors;
        for my $name (reverse @created) {
            eval { unlinkat_directory_cleanup($stage, $name,
                "transaction child $name"); 1 }
                or push @cleanup_errors, $@ || "cleanup child $name failed";
        }
        eval { unlinkat_directory_cleanup($parent, $staging,
            'transaction root'); 1 }
            or push @cleanup_errors, $@ || 'cleanup transaction root failed';
        sync_directory($parent, 'transaction rollback parent');
        $error .= 'cleanup failure: ' . join('; ', @cleanup_errors) . "\n"
            if @cleanup_errors;
        die $error;
    };
    return { parent => $parent, leaf => $leaf, staging => $staging,
        stage => $stage, child => \%child };
}

sub unlinkat_entry {
    my ($parent, $leaf, $flags, $name) = @_;
    syscall(&SYS_unlinkat, fileno($parent), $leaf, $flags) == 0
        or die "stage2 runner: remove $name: $!\n";
}

sub remove_tree_contents {
    my ($root, $name) = @_;
    my $path = '/proc/self/fd/' . fileno($root);
    opendir(my $dir, $path)
        or die "stage2 runner: enumerate $name: $!\n";
    my @entries = sort grep { $_ ne '.' && $_ ne '..' } readdir($dir);
    closedir($dir) or die "stage2 runner: close $name enumeration: $!\n";
    for my $leaf (@entries) {
        $leaf !~ m{/|\0} or die "stage2 runner: unsafe transaction entry\n";
        my $entry_path = "$path/$leaf";
        my @st = lstat($entry_path);
        @st or die "stage2 runner: stat $name/$leaf: $!\n";
        if (-d _ && !-l _) {
            my $child = open_child_directory($root, $leaf, "$name/$leaf");
            remove_tree_contents($child, "$name/$leaf");
            unlinkat_entry($root, $leaf, 0x200, "$name/$leaf");
        } else {
            unlinkat_entry($root, $leaf, 0, "$name/$leaf");
        }
    }
    sync_directory($root, "$name rollback");
}

sub rollback_transaction {
    my ($transaction) = @_;
    return 1 unless defined($transaction);
    remove_tree_contents($transaction->{stage}, 'transaction root');
    unlinkat_directory($transaction->{parent}, $transaction->{staging},
        'transaction root');
    sync_directory($transaction->{parent}, 'transaction rollback parent');
    return 1;
}
sub set_cloexec {
    my ($fh, $enabled) = @_;
    my $flags = fcntl($fh, F_GETFD, 0);
    defined($flags) or die "stage2 runner: cannot read descriptor flags: $!\n";
    $flags = $enabled ? ($flags | FD_CLOEXEC) : ($flags & ~FD_CLOEXEC);
    fcntl($fh, F_SETFD, $flags)
        or die "stage2 runner: cannot set close-on-exec: $!\n";
}
sub protect_descriptor {
    my ($fh, $mode, $name) = @_;
    my $protected_fd = fcntl($fh, F_DUPFD, 64);
    defined($protected_fd)
        or die "stage2 runner: protect $name descriptor: $!\n";
    my $protected = IO::Handle->new_from_fd($protected_fd, $mode);
    defined($protected)
        or die "stage2 runner: adopt protected $name descriptor: $!\n";
    set_cloexec($protected, 1);
    close($fh) or die "stage2 runner: close unprotected $name descriptor: $!\n";
    return $protected;
}
sub protect_transaction_handles {
    my ($transaction) = @_;
    $transaction->{parent} = protect_descriptor(
        $transaction->{parent}, 'r', 'transaction parent');
    $transaction->{stage} = protect_descriptor(
        $transaction->{stage}, 'r', 'transaction stage');
    for my $name (@transaction_children) {
        $transaction->{child}{$name} = protect_descriptor(
            $transaction->{child}{$name}, 'r', "transaction child $name");
    }

    my @stage = stat($transaction->{stage});
    @stage or die "stage2 runner: stat protected transaction stage: $!\n";
    my %child_identity;
    for my $name (@transaction_children) {
        my @child = stat($transaction->{child}{$name});
        @child or die "stage2 runner: stat protected transaction child $name: $!\n";
        my $identity = "$child[0]:$child[1]";
        !exists($child_identity{$identity})
            or die "stage2 runner: aliased transaction children $child_identity{$identity} and $name\n";
        $child_identity{$identity} = $name;
        !($child[0] == $stage[0] && $child[1] == $stage[1])
            or die "stage2 runner: transaction stage aliases child $name\n";
    }
    return $transaction;
}
sub close_descriptors_except {
    my (@keep) = @_;
    my %keep = map { $_ => 1 } @keep;
    opendir(my $dir, '/proc/self/fd')
        or die "stage2 runner: enumerate inherited descriptors: $!\n";
    my @close = grep { /^\d+$/ && $_ > 2 && !$keep{$_} } readdir($dir);
    closedir($dir) or die "stage2 runner: close descriptor directory: $!\n";
    POSIX::close($_) for @close;
}
sub open_root_descriptor {
    my ($path) = @_;
    normalized_absolute($path, 'root');
    sysopen(my $root, $path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW)
        or die "stage2 runner: open root descriptor: $!\n";
    set_cloexec($root, 1);
    my @held = stat($root); my @path = lstat($path); my @cwd = stat('.');
    @held && @path && @cwd && -d _ &&
        $held[0] == $path[0] && $held[1] == $path[1] &&
        $held[0] == $cwd[0] && $held[1] == $cwd[1]
        or die "stage2 runner: root descriptor/current-directory identity mismatch\n";
    return $root;
}
sub adopt_descriptor {
    my ($fd, $name) = @_;
    my $fh = IO::Handle->new_from_fd($fd, 'r+');
    defined($fh) or die "stage2 runner: adopt $name descriptor: $!\n";
    set_cloexec($fh, 1);
    my $flags = fcntl($fh, F_GETFD, 0);
    defined($flags) && ($flags & FD_CLOEXEC)
        or die "stage2 runner: $name descriptor is not close-on-exec\n";
    return $fh;
}
sub open_role_descriptor {
    my ($reference, $name) = @_;
    $reference =~ m{\A/proc/[1-9][0-9]*/fd/[0-9]+\z}
        or die "stage2 runner: invalid descriptor-pinned $name role\n";
    sysopen(my $fh, $reference, O_RDONLY)
        or die "stage2 runner: open $name role: $!\n";
    set_cloexec($fh, 1);
    my @st = stat($fh);
    @st && -f _ or die "stage2 runner: nonregular $name role\n";
    return $fh;
}
sub verify_outer_lock_descriptor {
    my ($fd, $path) = @_;
    defined($fd) && $fd >= 3
        or die "stage2 runner: supervisor lock descriptor is absent\n";
    normalized_absolute($path, 'outer lock path');
    -f $path && !-l $path or die "stage2 runner: outer lock path is invalid\n";
    my $held = adopt_descriptor($fd, 'outer lock capability');
    my @held = stat($held); my @path = lstat($path);
    @held && @path && $held[0] == $path[0] && $held[1] == $path[1]
        or die "stage2 runner: outer lock descriptor identity mismatch\n";
    my $fdinfo_path = '/proc/self/fdinfo/' . fileno($held);
    sysopen(my $fdinfo, $fdinfo_path, O_RDONLY | O_NOFOLLOW)
        or die "stage2 runner: open supplied lock fdinfo: $!\n";
    my $proof = do { local $/; <$fdinfo> };
    close($fdinfo) or die "stage2 runner: close supplied lock fdinfo: $!\n";
    defined($proof) && $proof =~ /^lock:\s+\d+:\s+FLOCK\s+ADVISORY\s+WRITE\s+/m
        or die "stage2 runner: supplied descriptor does not own heavy lock\n";
    return $held;
}
sub hash_fh {
    my ($fh, $name) = @_;
    my $position = sysseek($fh, 0, 1);
    defined($position) or die "stage2 runner: seek $name identity: $!\n";
    defined(sysseek($fh, 0, 0))
        or die "stage2 runner: rewind $name identity: $!\n";
    my $digest = Digest::SHA->new(256);
    while (1) {
        my $count = sysread($fh, my $bytes, 65_536);
        if (!defined($count)) {
            next if $! == EINTR;
            die "stage2 runner: read $name identity: $!\n";
        }
        last if $count == 0;
        $digest->add(substr($bytes, 0, $count));
    }
    defined(sysseek($fh, $position, 0))
        or die "stage2 runner: restore $name identity: $!\n";
    return $digest->hexdigest;
}
sub publish_at_exclusive {
    my ($parent, $leaf, $text, $name) = @_;
    my $path = '/proc/self/fd/' . fileno($parent) . "/$leaf";
    sysopen(my $fh, $path, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW, 0600)
        or die "stage2 runner: $name collision: $!\n";
    print {$fh} $text or die "stage2 runner: write result: $!\n";
    $fh->sync or die "stage2 runner: fsync $name: $!\n";
    close($fh) or die "stage2 runner: close $name: $!\n";
    sync_directory($parent, "$name parent");
}
sub hash_directory {
    my ($root, $name) = @_;
    my @before = stat($root);
    @before or die "stage2 runner: stat $name: $!\n";
    my $path = '/proc/self/fd/' . fileno($root);
    opendir(my $dir, $path)
        or die "stage2 runner: enumerate $name: $!\n";
    my @entries = sort grep { $_ ne '.' && $_ ne '..' } readdir($dir);
    closedir($dir) or die "stage2 runner: close $name enumeration: $!\n";
    my $digest = Digest::SHA->new(256);
    $digest->add("simple-stage2-directory-v1\0");
    for my $leaf (@entries) {
        $leaf !~ m{/|\0} or die "stage2 runner: unsafe $name entry\n";
        my $entry_path = "$path/$leaf";
        my @st = lstat($entry_path);
        @st or die "stage2 runner: stat $name/$leaf: $!\n";
        my $mode = sprintf('%04o', $st[2] & 07777);
        if (-d _ && !-l _) {
            my $child = open_child_directory($root, $leaf, "$name/$leaf");
            my @held = stat($child);
            @held && $held[0] == $st[0] && $held[1] == $st[1]
                or die "stage2 runner: changed directory $name/$leaf\n";
            my $hash = hash_directory($child, "$name/$leaf");
            $digest->add(join("\0", 'D', $leaf, $mode, $hash), "\0");
        } elsif (-f _ && !-l _) {
            sysopen(my $file, $entry_path, O_RDONLY | O_NOFOLLOW)
                or die "stage2 runner: open $name/$leaf: $!\n";
            set_cloexec($file, 1);
            my @held = stat($file);
            @held && $held[0] == $st[0] && $held[1] == $st[1]
                or die "stage2 runner: changed file $name/$leaf\n";
            my $hash = hash_fh($file, "$name/$leaf");
            $file->sync or die "stage2 runner: fsync $name/$leaf: $!\n";
            close($file) or die "stage2 runner: close $name/$leaf: $!\n";
            $digest->add(join("\0", 'F', $leaf, $mode, $st[7], $hash), "\0");
        } elsif (-l _) {
            my $target = readlink($entry_path);
            defined($target) or die "stage2 runner: read $name/$leaf link: $!\n";
            $digest->add(join("\0", 'L', $leaf, $mode, $target), "\0");
        } else {
            die "stage2 runner: unsupported entry $name/$leaf\n";
        }
    }
    sync_directory($root, $name);
    my @after = stat($root);
    @after && $before[0] == $after[0] && $before[1] == $after[1] &&
        $before[9] == $after[9] && $before[10] == $after[10]
        or die "stage2 runner: $name changed while freezing\n";
    return $digest->hexdigest;
}
sub publish_transaction {
    my ($transaction, $status, $source_rows) = @_;
    my $outcome = join('',
        "schema=simple-bootstrap-stage2-runner-v4\n",
        "status=" . ($status == 0 ? 'succeeded' : 'failed') . "\n",
        "exit_code=$status\n",
        "compiler_wall_ms=$o{compiler_wall_ms}\n",
        "wall_scope=stage2-compiler-native-build-only\n", "jobs=16\n",
        "memory_max_bytes=$o{memory_max}\n",
        "memory_authority=outer-supervisor\n",
        "lock_authority=outer-supervisor-descriptor-verified\n",
        "descendant_cleanup_authority=outer-cgroup\n",
        "runner_zero_proof=not-claimed\n");
    publish_at_exclusive($transaction->{child}{evidence}, 'result.env',
        $outcome, 'outcome receipt');
    my @child_rows;
    for my $name (@transaction_children) {
        my $fh = $transaction->{child}{$name};
        my @st = stat($fh);
        @st or die "stage2 runner: stat transaction child $name: $!\n";
        my $hash = hash_directory($fh, "transaction child $name");
        push @child_rows,
            "child=$name dev=$st[0] ino=$st[1] content_sha256=$hash\n";
    }
    my $transaction_text = join('',
        "schema=simple-bootstrap-stage2-transaction-v1\n",
        "status=committed\n", "exit_code=$status\n",
        @$source_rows, @child_rows,
        "outcome=evidence/result.env\n",
        "outcome_sha256=" . sha256_hex($outcome) . "\n");
    # This is deliberately the final staging-tree write.  Its fsync, followed
    # by the root-directory fsync, precedes the sole externally visible rename.
    publish_at_exclusive($transaction->{stage}, 'transaction.env',
        $transaction_text, 'transaction receipt');
    sync_directory($transaction->{stage}, 'transaction root');
    renameat_noreplace($transaction->{parent}, $transaction->{staging},
        $transaction->{parent}, $transaction->{leaf}, 'transaction root');
    # From this instruction onward the staging name no longer exists.  Mark
    # publication before the durability fence so failure cleanup can never
    # remove or reinterpret the committed transaction through its old name.
    $transaction->{published} = 1;
    sync_directory($transaction->{parent}, 'transaction parent');
}
sub decoded_status {
    my ($status) = @_;
    return 128 + ($status & 127) if $status & 127;
    return $status >> 8;
}
sub child_fail {
    my ($fh, $message) = @_;
    my $offset = 0;
    while ($offset < length($message)) {
        my $written = syswrite($fh, $message, length($message) - $offset,
            $offset);
        next if !defined($written) && $! == EINTR;
        last unless defined($written) && $written > 0;
        $offset += $written;
    }
    POSIX::_exit(126);
}
sub reap_failed_child {
    my ($pid) = @_;
    return unless defined($pid);
    kill('TERM', -$pid); kill('TERM', $pid);
    while (waitpid($pid, 0) < 0) {
        next if $! == EINTR;
        last;
    }
}

for my $key (qw(root transaction_root bootstrap outer_lock_path)) {
    defined($o{$key}) && length($o{$key}) or die "stage2 runner: missing --$key\n";
}
$0 =~ m{\A/} or die "stage2 runner: invoke through an absolute path\n";
defined($o{legacy_wall_ms})
    and die "stage2 runner: --stage2-wall-ms is obsolete; deadline is compiler-phase only\n";
$o{compiler_wall_ms} == 3_600_000 || $o{allow_test_hooks}
    or die "stage2 runner: compiler wall must remain 3600000ms\n";
$o{memory_max} == 53_687_091_200
    or die "stage2 runner: memory authority must remain 53687091200 bytes\n";
$o{dash} eq '/usr/bin/dash' || $o{allow_test_hooks}
    or die "stage2 runner: payload interpreter must remain /usr/bin/dash\n";
-d $o{root} && !-l $o{root} && (realpath($o{root}) // '') eq $o{root}
    or die "stage2 runner: invalid root\n";
(($ENV{SIMPLE_STAGE3_OUTER_LOCK_HELD} // '') eq '1')
    or die "stage2 runner: supervisor outer-lock authority is absent\n";
defined($o{outer_lock_fd}) &&
    (($ENV{SIMPLE_STAGE3_HEAVY_LOCK_CAPABILITY_FD} // '') eq
        "$o{outer_lock_fd}")
    or die "stage2 runner: heavy-lock capability descriptor is unauthenticated\n";
$o{outer_lock_fd} == 9 || $o{allow_test_hooks}
    or die "stage2 runner: production heavy-lock capability must use descriptor 9\n";
for my $private_marker (qw(SIMPLE_BOOTSTRAP_STAGE2_RUNNER_PRIVATE
        SIMPLE_BOOTSTRAP_OUTER_LOCK_PROOF SIMPLE_BOOTSTRAP_OUTER_LOCK_CONTROL_FD
        SIMPLE_BOOTSTRAP_DELEGATED_REPO_ROOT
        SIMPLE_BOOTSTRAP_DELEGATED_SCRIPT_PATH
        SIMPLE_BOOTSTRAP_STAGE2_TRANSACTION_ROOT
        SIMPLE_BOOTSTRAP_STAGE2_EVIDENCE_DIR)) {
    exists($ENV{$private_marker})
        and die "stage2 runner: private marker was supplied by caller\n";
}
my $child_fail_point = $o{allow_test_hooks}
    ? ($ENV{STAGE2_RUNNER_TEST_CHILD_FAIL} // '') : '';
$child_fail_point =~ /\A(?:|setpgid|chdir)\z/
    or die "stage2 runner: invalid child failure hook\n";
for my $pair ([SIMPLE_BOOTSTRAP_BUILD_JOBS => '16'],
        [SIMPLE_BOOTSTRAP_MAX_BUILD_JOBS => '16'],
        [SIMPLE_NO_STUB_FALLBACK => '1']) {
    ($ENV{$pair->[0]} // '') eq $pair->[1]
        or die "stage2 runner: frozen environment mismatch for $pair->[0]\n";
}
my $held_lock = protect_descriptor(verify_outer_lock_descriptor(
    $o{outer_lock_fd}, $o{outer_lock_path}), 'r+', 'outer lock capability');
my $root_fh = protect_descriptor(open_root_descriptor($o{root}),
    'r', 'root');
my $bootstrap_fh = protect_descriptor(
    open_role_descriptor($o{bootstrap}, 'bootstrap'), 'r', 'bootstrap');
my @bootstrap_identity = stat($bootstrap_fh);
@bootstrap_identity or die "stage2 runner: stat bootstrap identity: $!\n";
my $bootstrap_hash = hash_fh($bootstrap_fh, 'bootstrap');

my @expected_helpers = qw(session planner_admission cache_policy jobs_policy
    provenance_facade provenance_authority provenance_command provenance_sanity
    provenance_manifest_write provenance_manifest_verify provenance_self_test
    portable_lock_atomic portable_process_lock authority_wiring stage4_provenance
    resume_stage4 progress_watch platform_detect candidate_frontend preserve_phase
    stage2_receiver stage_log compiler_deadline);
@helper == @expected_helpers or die "stage2 runner: incomplete helper capsule\n";
my @helper_sources;
my (@source_rows);
push @source_rows,
    "bootstrap_dev=$bootstrap_identity[0]\n",
    "bootstrap_ino=$bootstrap_identity[1]\n",
    "bootstrap_sha256=$bootstrap_hash\n";
for my $index (0 .. $#expected_helpers) {
    my $name = $expected_helpers[$index];
    $helper[$index] =~ /\A\Q$name\E=(\/proc\/[1-9][0-9]*\/fd\/[0-9]+)\z/
        or die "stage2 runner: invalid or reordered helper $name\n";
    my $source = protect_descriptor(
        open_role_descriptor($1, "helper $name"), 'r', "helper $name");
    my @identity = stat($source);
    @identity or die "stage2 runner: stat helper $name identity: $!\n";
    my $hash = hash_fh($source, "helper $name");
    push @source_rows,
        "helper=$name dev=$identity[0] ino=$identity[1] sha256=$hash\n";
    push @helper_sources, $source;
}

# All source capabilities are first moved above the reserved range.  Only then
# may fixed destinations be populated, so an inherited source already at
# 6/7/8/9 (or at a helper destination) cannot be overwritten before capture.
defined(dup2(fileno($bootstrap_fh), 6))
    or die "stage2 runner: pin bootstrap descriptor 6: $!\n";
defined(dup2(fileno($root_fh), 8))
    or die "stage2 runner: pin root descriptor 8: $!\n";
my $bootstrap_fixed = IO::Handle->new_from_fd(6, 'r');
my $root_fixed = IO::Handle->new_from_fd(8, 'r');
defined($bootstrap_fixed) && defined($root_fixed)
    or die "stage2 runner: adopt fixed bootstrap/root descriptors: $!\n";
set_cloexec($bootstrap_fixed, 1); set_cloexec($root_fixed, 1);
close($bootstrap_fh) or die "stage2 runner: close protected bootstrap: $!\n";
close($root_fh) or die "stage2 runner: close protected root: $!\n";

my (%helper_fixed, @helper_fixed_fh);
for my $index (0 .. $#expected_helpers) {
    my $name = $expected_helpers[$index];
    my $source = $helper_sources[$index];
    my $fixed = 20 + $index;
    defined(dup2(fileno($source), $fixed))
        or die "stage2 runner: pin helper $name descriptor: $!\n";
    my $held = IO::Handle->new_from_fd($fixed, 'r');
    defined($held) or die "stage2 runner: adopt helper $name descriptor: $!\n";
    set_cloexec($held, 1);
    $helper_fixed{$name} = $fixed;
    push @helper_fixed_fh, $held;
    close($source)
        or die "stage2 runner: close protected helper $name: $!\n";
}
close_descriptors_except(6, 8, fileno($held_lock), values %helper_fixed);

# One absent leaf is the entire mutable authority.  No independently resolved
# output/evidence/private path exists in this contract.
preflight_absent($o{transaction_root}, 'transaction root');

my $transaction;
my $child_pid;
eval {
    sysopen(my $transaction_reserve, '/dev/null', O_RDONLY | O_NOFOLLOW)
        or die "stage2 runner: reserve transaction descriptor 10: $!\n";
    if (fileno($transaction_reserve) != 10) {
        defined(dup2(fileno($transaction_reserve), 10))
            or die "stage2 runner: reserve fixed transaction descriptor 10: $!\n";
        close($transaction_reserve)
            or die "stage2 runner: close transaction reserve source: $!\n";
        $transaction_reserve = IO::Handle->new_from_fd(10, 'r');
        defined($transaction_reserve)
            or die "stage2 runner: adopt transaction reserve descriptor: $!\n";
    }
    set_cloexec($transaction_reserve, 1);
    $transaction = protect_transaction_handles(
        create_transaction($o{transaction_root}));
    defined(dup2(fileno($transaction->{stage}), 10))
        or die "stage2 runner: pin transaction descriptor 10: $!\n";
    my $transaction_fixed = IO::Handle->new_from_fd(10, 'r');
    defined($transaction_fixed)
        or die "stage2 runner: adopt transaction descriptor 10: $!\n";
    set_cloexec($transaction_fixed, 1);

    pipe(my $control_r, my $control_w)
        or die "stage2 runner: create lock-control pipe: $!\n";
    set_cloexec($control_r, 1); set_cloexec($control_w, 1);
    my @lock_identity = stat($held_lock);
    @lock_identity or die "stage2 runner: stat held lock capability: $!\n";
    my $control = join('', "schema=simple-stage2-lock-control-v1\n",
        "status=verified-before-fork\n", "lock_dev=$lock_identity[0]\n",
        "lock_ino=$lock_identity[1]\n");
    print {$control_w} $control or die "stage2 runner: write lock control: $!\n";
    close($control_w) or die "stage2 runner: close lock control writer: $!\n";
    $control_r = protect_descriptor($control_r, 'r', 'lock control');
    pipe(my $exec_r, my $exec_w)
        or die "stage2 runner: create exec-status pipe: $!\n";
    set_cloexec($exec_w, 1);
    $exec_w = protect_descriptor($exec_w, 'w', 'exec status');
    my @command = ($o{dash}, '-s', '--', '--full-bootstrap',
        '--stop-after-stage2', '--strategy=normal', '--backend=cranelift',
        '--mode=dynload', '--jobs=16', '--output=/proc/self/fd/10/output');
    my $pid = fork();
    defined($pid) or die "stage2 runner: fork: $!\n";
    $child_pid = $pid if $pid;
    if (!$pid) {
        close($exec_r);
        $child_fail_point eq 'setpgid'
            and child_fail($exec_w, "setpgid:injected");
        defined(setpgid(0, 0)) or child_fail($exec_w, "setpgid:$!");
        $child_fail_point eq 'chdir'
            and child_fail($exec_w, "chdir:injected");
        chdir($root_fixed) or child_fail($exec_w, "chdir:$!");
        defined(dup2(fileno($control_r), 7))
            or child_fail($exec_w, "dup2-lock-control:$!");
        my $bootstrap_exec = IO::Handle->new_from_fd(6, 'r');
        my $control_exec = IO::Handle->new_from_fd(7, 'r');
        my $root_exec = IO::Handle->new_from_fd(8, 'r');
        my $transaction_exec = IO::Handle->new_from_fd(10, 'r');
        defined($bootstrap_exec) && defined($control_exec) && defined($root_exec) &&
            defined($transaction_exec)
            or child_fail($exec_w, "adopt-fixed-role:$!");
        set_cloexec($bootstrap_exec, 0);
        set_cloexec($control_exec, 0);
        set_cloexec($root_exec, 0);
        set_cloexec($transaction_exec, 0);
        set_cloexec($_, 0) for @helper_fixed_fh;
        defined(dup2(fileno($bootstrap_exec), 0))
            or child_fail($exec_w, "dup2-bootstrap-stdin:$!");
        $ENV{HOME} = '/proc/self/fd/10/home';
        $ENV{TMPDIR} = '/proc/self/fd/10/tmp';
        $ENV{SIMPLE_NATIVE_BUILD_CACHE_DIR} = '/proc/self/fd/10/cache';
        $ENV{SIMPLE_BOOTSTRAP_STAGE2_RUNNER_PRIVATE} = '1';
        $ENV{SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED} = '1';
        $ENV{SIMPLE_BOOTSTRAP_OUTER_LOCK_PROOF} = 'descriptor-verified-v1';
        $ENV{SIMPLE_BOOTSTRAP_OUTER_LOCK_CONTROL_FD} = '7';
        $ENV{SIMPLE_BOOTSTRAP_DELEGATED_REPO_ROOT} = '/proc/self/fd/8';
        $ENV{SIMPLE_BOOTSTRAP_DELEGATED_SCRIPT_PATH} = '/proc/self/fd/6';
        $ENV{SIMPLE_BOOTSTRAP_STAGE2_TRANSACTION_ROOT} = '/proc/self/fd/10';
        $ENV{SIMPLE_BOOTSTRAP_STAGE2_EVIDENCE_DIR} =
            '/proc/self/fd/10/evidence';
        for my $name (@expected_helpers) {
            my $key = uc($name); $key =~ tr/-/_/;
            $ENV{"SIMPLE_BOOTSTRAP_STAGE2_HELPER_$key"} =
                "/proc/self/fd/$helper_fixed{$name}";
        }
        $ENV{SIMPLE_BOOTSTRAP_STAGE2_COMPILER_WALL_MS} =
            "$o{compiler_wall_ms}";
        exec @command;
        child_fail($exec_w, "exec:$!");
    }
    close($control_r) or die "stage2 runner: close lock control reader: $!\n";
    close($exec_w);
    my $exec_error = '';
    while (1) {
        my $count = sysread($exec_r, my $chunk, 256);
        if (!defined($count)) {
            next if $! == EINTR;
            die "stage2 runner: read exec status: $!\n";
        }
        last if $count == 0;
        $exec_error .= $chunk;
    }
    close($exec_r);
    if (length($exec_error)) {
        reap_failed_child($pid);
        undef $child_pid;
        die "stage2 runner: child pre-exec failure: $exec_error\n";
    }
    my $waited;
    while (($waited = waitpid($pid, 0)) < 0) {
        next if $! == EINTR;
        die "stage2 runner: waitpid: $!\n";
    }
    $waited == $pid or die "stage2 runner: reaped unexpected child\n";
    undef $child_pid;
    my $status = decoded_status($?);
    publish_transaction($transaction, $status, \@source_rows);
    exit($status);
};
my $error = $@ || "stage2 runner: unknown failure\n";
reap_failed_child($child_pid) if defined($child_pid);
rollback_transaction($transaction)
    if defined($transaction) && !$transaction->{published};
die $error;
