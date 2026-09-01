#!/usr/bin/env perl
use strict;
use warnings;
use Config;
use Digest::SHA qw(sha256_hex);
use Errno qw(EINTR EEXIST ESRCH ECHILD EACCES EPERM ENOENT);
use Fcntl qw(:DEFAULT :mode F_GETFD F_SETFD FD_CLOEXEC O_NOFOLLOW O_DIRECTORY);
use File::Basename qw(dirname);
use Getopt::Long qw(GetOptions);
use IO::Handle;
use POSIX qw(WNOHANG SIG_BLOCK SIGTERM SIGINT SIGHUP SIGQUIT
    sigprocmask sigpending);
use Time::HiRes qw(clock_gettime sleep CLOCK_MONOTONIC);

my $O_CLOEXEC = 02000000;
my $O_TMPFILE = 020200000;
my $AT_SYMLINK_FOLLOW = 0x400;
my ($SYS_OPENAT, $SYS_LINKAT) = $Config{archname} =~ /(?:aarch64|riscv64)/
    ? (56, 37) : $Config{archname} =~ /x86_64/ ? (257, 265) : (0, 0);
my @original_argv = @ARGV;
my %o;
GetOptions(
    'payload-exec=s' => \$o{payload_exec}, 'runner-exec=s' => \$o{runner_exec},
    'root=s' => \$o{root}, 'unit-evidence=s' => \$o{unit_evidence},
    'active-cgroup-receipt=s' => \$o{active_cgroup_receipt},
    'run-id=s' => \$o{run_id}, 'architecture=s' => \$o{architecture},
    'source-output=s' => \$o{source_output},
    'stage2-transaction-root=s' => \$o{stage2_transaction_root},
    'compatibility-marker=s' => \$o{compatibility_marker},
    'raw=s' => \$o{raw}, 'descriptor=s' => \$o{descriptor},
    'parent-provenance=s' => \$o{parent_provenance},
    'parent-provenance-verify-receipt=s' => \$o{parent_provenance_verify},
    'source-snapshot=s' => \$o{source_snapshot},
    'git-receipt=s' => \$o{git_receipt},
    'runtime-snapshot=s' => \$o{runtime_snapshot},
    'tool-snapshot=s' => \$o{tool_snapshot},
    'stage2-admission=s' => \$o{stage2_admission},
    'planner-receipt=s' => \$o{planner_receipt},
    'candidate-output=s' => \$o{candidate_output},
    'candidate-provenance=s' => \$o{candidate_provenance},
    'facade=s' => \$o{facade},
    'systemd-run=s' => \$o{systemd_run},
    'systemd-run-sha256=s' => \$o{systemd_run_sha256},
    'systemctl=s' => \$o{systemctl},
    'systemctl-sha256=s' => \$o{systemctl_sha256},
    'sampler-exec=s' => \$o{sampler_exec},
    'sampler-sha256=s' => \$o{sampler_sha256},
    'analyzer-exec=s' => \$o{analyzer_exec},
    'analyzer-sha256=s' => \$o{analyzer_sha256},
    'admitted-compiler=s' => \$o{admitted_compiler},
    'admitted-compiler-sha256=s' => \$o{admitted_compiler_sha256},
    'dash-exec=s' => \$o{dash_exec},
    'dash-sha256=s' => \$o{dash_sha256},
    'candidate-builder-sha256=s' => \$o{candidate_builder_sha256},
    'runner-sha256=s' => \$o{runner_sha256},
    'provenance-verifier-sha256=s' => \$o{provenance_verifier_sha256},
) or die "stage3 shared runner: invalid options\n";

my $parent_pid = $$;
my $candidate_builder_pid;
my $active_pid;
my $active_pgid;
my $interrupted = '';
my $console_fh;
my $unit_evidence_dir_fh;
my %held;
my $verifier_scratch_parent;
my $verifier_scratch_path;
my $terminal_signal_set = POSIX::SigSet->new(SIGTERM, SIGINT, SIGHUP, SIGQUIT);

sub now_ms { int(clock_gettime(CLOCK_MONOTONIC) * 1000) }
sub valid_sha { defined($_[0]) && $_[0] =~ /\A[0-9a-f]{64}\z/ }
sub valid_run_id {
    defined($_[0]) && $_[0] =~ /\A[A-Za-z0-9_-]{8,64}\z/;
}
sub normalized_absolute {
    my ($path) = @_;
    return 0 unless defined($path) && $path =~ m{\A/} && $path ne '/' &&
        length($path) <= 16_384 && $path !~ /[\x00-\x1f\x7f]/ &&
        $path !~ /\\/ && $path !~ m{/$};
    for my $part (split m{/}, substr($path, 1), -1) {
        return 0 if $part eq '' || $part eq '.' || $part eq '..';
    }
    return 1;
}
sub absolute_dir {
    my ($path) = @_;
    my $fh = open_directory_walk($path);
    close($fh) or die "stage3 shared runner: close directory $path: $!\n";
}
sub set_cloexec {
    my ($fh) = @_;
    my $flags = fcntl($fh, F_GETFD, 0);
    defined($flags) or die "stage3 shared runner: read descriptor flags: $!\n";
    fcntl($fh, F_SETFD, $flags | FD_CLOEXEC)
        or die "stage3 shared runner: set descriptor flags: $!\n";
}
sub hash_fh {
    my ($fh) = @_;
    seek($fh, 0, 0) or die "stage3 shared runner: seek hash descriptor: $!\n";
    my $sha = Digest::SHA->new(256);
    $sha->addfile($fh);
    seek($fh, 0, 0) or die "stage3 shared runner: rewind hash descriptor: $!\n";
    return $sha->hexdigest;
}
sub descriptor_handle {
    my ($fd, $kind, $writable) = @_;
    $fd >= 0 or die "stage3 shared runner: $kind: $!\n";
    open(my $fh, $writable ? '+<&=' : '<&=', $fd)
        or die "stage3 shared runner: adopt $kind descriptor: $!\n";
    set_cloexec($fh);
    return $fh;
}
sub open_directory_walk {
    my ($path) = @_;
    normalized_absolute($path)
        or die "stage3 shared runner: noncanonical directory path\n";
    $SYS_OPENAT or die "stage3 shared runner: unsupported syscall architecture\n";
    sysopen(my $current, '/', O_RDONLY | O_DIRECTORY | O_NOFOLLOW | $O_CLOEXEC)
        or die "stage3 shared runner: open root directory: $!\n";
    set_cloexec($current);
    for my $part (split m{/}, substr($path, 1), -1) {
        my $fd = syscall($SYS_OPENAT, fileno($current), $part,
            O_RDONLY | O_DIRECTORY | O_NOFOLLOW | $O_CLOEXEC, 0);
        my $next = descriptor_handle($fd, "open directory component $part");
        close($current)
            or die "stage3 shared runner: close walked directory: $!\n";
        $current = $next;
    }
    my @st = stat($current);
    @st && -d _ or die "stage3 shared runner: walked non-directory\n";
    return $current;
}
sub read_fh_text {
    my ($fh, $max_bytes) = @_;
    my @st = stat($fh);
    @st && $st[7] > 0 && $st[7] <= $max_bytes
        or die "stage3 shared runner: retained text size invalid\n";
    seek($fh, 0, 0) or die "stage3 shared runner: seek retained text: $!\n";
    local $/;
    my $text = <$fh>;
    defined($text) && length($text) == $st[7]
        or die "stage3 shared runner: read retained text: $!\n";
    seek($fh, 0, 0) or die "stage3 shared runner: rewind retained text: $!\n";
    return $text;
}
sub open_regular {
    my ($path, $expected_sha) = @_;
    normalized_absolute($path)
        or die "stage3 shared runner: noncanonical file path\n";
    my $parent = open_directory_walk(dirname($path));
    my $leaf = substr($path, length(dirname($path)) +
        (dirname($path) eq '/' ? 0 : 1));
    $leaf =~ /\A[^\/]+\z/ or die "stage3 shared runner: invalid file leaf\n";
    my $fd = syscall($SYS_OPENAT, fileno($parent), $leaf,
        O_RDONLY | O_NOFOLLOW | $O_CLOEXEC, 0);
    my $fh = descriptor_handle($fd, "open $path");
    close($parent) or die "stage3 shared runner: close file parent: $!\n";
    my @st = stat($fh);
    @st && -f _ or die "stage3 shared runner: nonregular file $path\n";
    my $sha = hash_fh($fh);
    if (defined($expected_sha)) {
        valid_sha($expected_sha) && $sha eq $expected_sha
            or die "stage3 shared runner: hash mismatch for $path\n";
    }
    return ($fh, { path => $path, dev => $st[0], ino => $st[1], sha256 => $sha });
}
sub open_directory_descriptor {
    my ($path) = @_;
    sysopen(my $fh, $path,
        O_RDONLY | O_DIRECTORY | O_NOFOLLOW | $O_CLOEXEC)
        or die "stage3 shared runner: open helper directory $path: $!\n";
    set_cloexec($fh);
    my @st = stat($fh);
    @st && -d _ or die "stage3 shared runner: helper ancestor is not a directory\n";
    return $fh;
}
sub open_root_relative {
    my ($root_fh, $relative) = @_;
    defined($relative) && $relative !~ m{\A/} &&
        $relative !~ /[\x00-\x1f\x7f\\]/ && length($relative) <= 16_384
        or die "stage3 shared runner: invalid helper relative path\n";
    my @part = split m{/}, $relative, -1;
    @part > 1 or die "stage3 shared runner: helper path lacks ancestor\n";
    for my $part (@part) {
        length($part) && $part ne '.' && $part ne '..'
            or die "stage3 shared runner: invalid helper path component\n";
    }
    my $current = $root_fh;
    my @opened;
    for my $index (0 .. $#part - 1) {
        my $next = open_directory_descriptor(
            '/proc/self/fd/' . fileno($current) . '/' . $part[$index]);
        push @opened, $next;
        $current = $next;
    }
    my $leaf = '/proc/self/fd/' . fileno($current) . '/' . $part[-1];
    sysopen(my $fh, $leaf, O_RDONLY | O_NOFOLLOW | $O_CLOEXEC)
        or die "stage3 shared runner: open helper $relative: $!\n";
    set_cloexec($fh);
    my @st = stat($fh);
    @st && -f _ or die "stage3 shared runner: helper is not regular $relative\n";
    my $identity = {
        path => "$o{root}/$relative", dev => $st[0], ino => $st[1],
        sha256 => hash_fh($fh),
    };
    for my $dir (reverse @opened) {
        close($dir) or die "stage3 shared runner: close helper ancestor: $!\n";
    }
    return ($fh, $identity);
}
sub open_optional_root_relative {
    my ($root_fh, $relative) = @_;
    defined($relative) && $relative !~ m{\A/} &&
        $relative !~ /[\x00-\x1f\x7f\\]/ && length($relative) <= 16_384
        or die "stage3 shared runner: invalid optional relative path\n";
    my @part = split m{/}, $relative, -1;
    @part > 1 && !grep { $_ eq '' || $_ eq '.' || $_ eq '..' } @part
        or die "stage3 shared runner: invalid optional path component\n";
    my $current = $root_fh;
    my @opened;
    for my $index (0 .. $#part - 1) {
        my $next = open_directory_descriptor(
            '/proc/self/fd/' . fileno($current) . '/' . $part[$index]);
        push @opened, $next; $current = $next;
    }
    my $fd = syscall($SYS_OPENAT, fileno($current), $part[-1],
        O_RDONLY | O_NOFOLLOW | $O_CLOEXEC, 0);
    if ($fd < 0) {
        my $missing = $! == ENOENT;
        for my $dir (reverse @opened) { close($dir) or die
            "stage3 shared runner: close optional ancestor: $!\n"; }
        return if $missing;
        die "stage3 shared runner: open optional $relative: $!\n";
    }
    my $fh = descriptor_handle($fd, "open optional $relative");
    my @st = stat($fh);
    @st && -f _ or die "stage3 shared runner: optional input is not regular\n";
    my $identity = { path => "$o{root}/$relative", dev => $st[0],
        ino => $st[1], mode => $st[2], sha256 => hash_fh($fh) };
    for my $dir (reverse @opened) { close($dir) or die
        "stage3 shared runner: close optional ancestor: $!\n"; }
    return ($fh, $identity);
}
sub open_relative_directory {
    my ($root_fh, $relative, $display_root) = @_;
    defined($relative) && $relative !~ m{\A/} &&
        $relative !~ /[\x00-\x1f\x7f\\]/ && length($relative) <= 16_384
        or die "stage3 shared runner: invalid relative directory\n";
    my @part = split m{/}, $relative, -1;
    @part && !grep { $_ eq '' || $_ eq '.' || $_ eq '..' } @part
        or die "stage3 shared runner: invalid relative directory component\n";
    my $current = $root_fh;
    my @opened;
    for my $part (@part) {
        my $next = open_directory_descriptor(
            '/proc/self/fd/' . fileno($current) . '/' . $part);
        push @opened, $next;
        $current = $next;
    }
    my @st = stat($current);
    my $identity = { path => "$display_root/$relative", dev => $st[0],
        ino => $st[1], mode => $st[2], directory => 1 };
    for my $index (0 .. $#opened - 1) {
        close($opened[$index])
            or die "stage3 shared runner: close relative directory ancestor: $!\n";
    }
    return ($opened[-1], $identity);
}
sub procfd_directory {
    my ($path, $kind) = @_;
    defined($path) && $path =~ m{\A/proc/[1-9][0-9]*/fd/[0-9]+\z}
        or die "stage3 shared runner: $kind is not a procfd directory\n";
    my $fh = open_directory_descriptor($path);
    return ($fh, directory_identity($fh));
}
sub absent_output_leaf {
    my ($path, $name) = @_;
    normalized_absolute($path)
        or die "stage3 shared runner: invalid $name output path\n";
    !-e $path && !-l $path
        or die "stage3 shared runner: $name output collision\n";
    my $parent = open_directory_walk(dirname($path));
    my $leaf = substr($path, length(dirname($path)) +
        (dirname($path) eq '/' ? 0 : 1));
    $leaf =~ /\A[A-Za-z0-9_.-]+\z/
        or die "stage3 shared runner: invalid $name output leaf\n";
    return ($parent, '/proc/' . $$ . '/fd/' . fileno($parent) . "/$leaf");
}
sub open_exec_reference {
    my ($reference, $regular_path, $expected_sha) = @_;
    $reference =~ m{\A/proc/[1-9][0-9]*/fd/[0-9]+\z}
        or die "stage3 shared runner: executable is not a retained descriptor\n";
    sysopen(my $exec_fh, $reference, O_RDONLY | $O_CLOEXEC)
        or die "stage3 shared runner: open executable descriptor: $!\n";
    set_cloexec($exec_fh);
    my ($regular_fh, $identity) = open_regular($regular_path, $expected_sha);
    my @est = stat($exec_fh);
    @est && $est[0] == $identity->{dev} && $est[1] == $identity->{ino} &&
        hash_fh($exec_fh) eq $identity->{sha256}
        or die "stage3 shared runner: descriptor/path identity mismatch\n";
    close($regular_fh) or die "stage3 shared runner: close identity file: $!\n";
    return ($exec_fh, $identity);
}
sub stable_identity {
    my ($fh, $identity) = @_;
    my @st = stat($fh);
    return @st && -d _ && $st[0] == $identity->{dev} &&
        $st[1] == $identity->{ino}
        if $identity->{directory};
    return @st && -f _ && $st[0] == $identity->{dev} &&
        $st[1] == $identity->{ino} && hash_fh($fh) eq $identity->{sha256};
}
sub directory_identity {
    my ($fh) = @_;
    my @st = stat($fh);
    @st && -d _ or die "stage3 shared runner: directory identity missing\n";
    return { dev => $st[0], ino => $st[1], directory => 1 };
}
sub vector_hash {
    my (@values) = @_;
    my $bytes = '';
    for my $value (@values) { $bytes .= pack('Q>', length($value)) . $value; }
    return sha256_hex($bytes);
}
sub token_v2 {
    my ($value) = @_;
    defined($value) && length($value)
        or die "stage3 shared runner: empty canonical token\n";
    my $singleton_dash = $value eq '-';
    my $encoded = '';
    for my $byte (unpack('C*', $value)) {
        if ($singleton_dash || $byte < 0x21 || $byte > 0x7e ||
                $byte == ord('%') || $byte == ord('=')) {
            $encoded .= sprintf('%%%02X', $byte);
        } else {
            $encoded .= chr($byte);
        }
    }
    return $encoded;
}
sub fsync_dir {
    my ($path) = @_;
    my $dfh = open_directory_walk($path);
    $dfh->sync or die "stage3 shared runner: fsync directory $path: $!\n";
    close($dfh) or die "stage3 shared runner: close directory $path: $!\n";
}
sub publish_exclusive_at {
    my ($dir_fh, $leaf, $text, $mode) = @_;
    $leaf =~ /\A[A-Za-z0-9._-]+\z/
        or die "stage3 shared runner: invalid publication leaf\n";
    my $tmp = ".$leaf.tmp.$parent_pid." . int(rand(1_000_000_000));
    my $fd = syscall($SYS_OPENAT, fileno($dir_fh), $tmp,
        O_RDWR | O_CREAT | O_EXCL | O_NOFOLLOW | $O_CLOEXEC, $mode // 0600);
    my $fh = descriptor_handle($fd, "create $tmp", 1);
    my $offset = 0;
    while ($offset < length($text)) {
        my $wrote = syswrite($fh, $text, length($text) - $offset, $offset);
        if (!defined($wrote)) { next if $! == EINTR; die "write $tmp: $!\n"; }
        $wrote > 0 or die "stage3 shared runner: zero write to $tmp\n";
        $offset += $wrote;
    }
    $fh->sync or die "stage3 shared runner: fsync $tmp: $!\n";
    my @st = stat($fh);
    @st && -f _ or die "stage3 shared runner: publication inode invalid\n";
    my $identity = { dev => $st[0], ino => $st[1], sha256 => hash_fh($fh) };
    close($fh) or die "stage3 shared runner: close $tmp: $!\n";
    my $base = '/proc/self/fd/' . fileno($dir_fh);
    link("$base/$tmp", "$base/$leaf") or do {
        my $error = "$!";
        unlink("$base/$tmp")
            or die "stage3 shared runner: rollback $tmp: $!\n";
        $dir_fh->sync or die "stage3 shared runner: fsync collision rollback: $!\n";
        die "stage3 shared runner: publication collision: $error\n";
    };
    $dir_fh->sync or die "stage3 shared runner: fsync publication directory: $!\n";
    unlink("$base/$tmp") or die "stage3 shared runner: remove $tmp: $!\n";
    $dir_fh->sync or die "stage3 shared runner: fsync publication cleanup: $!\n";
    return $identity;
}
sub anonymous_pass_inode {
    my ($dir_fh, $text, $mode) = @_;
    my $dot = '.';
    my $fd = syscall($SYS_OPENAT, fileno($dir_fh), $dot,
        $O_TMPFILE | O_RDWR | $O_CLOEXEC, $mode // 0600);
    my $fh = descriptor_handle($fd, 'create anonymous PASS inode', 1);
    my $offset = 0;
    while ($offset < length($text)) {
        my $wrote = syswrite($fh, $text, length($text) - $offset, $offset);
        if (!defined($wrote)) { next if $! == EINTR; die "write PASS inode: $!\n"; }
        $wrote > 0 or die "stage3 shared runner: zero write to PASS inode\n";
        $offset += $wrote;
    }
    $fh->sync or die "stage3 shared runner: fsync PASS inode: $!\n";
    return $fh;
}
sub link_anonymous_final {
    my ($file_fh, $dir_fh, $leaf) = @_;
    $leaf =~ /\A[A-Za-z0-9._-]+\z/
        or die "stage3 shared runner: invalid canonical PASS leaf\n";
    my $source = '/proc/self/fd/' . fileno($file_fh);
    my $result = syscall($SYS_LINKAT, -100, $source, fileno($dir_fh),
        $leaf, $AT_SYMLINK_FOLLOW);
    $result == 0 or die "stage3 shared runner: canonical PASS collision: $!\n";
}
sub prepare_canonical_pass_at {
    my ($dir_fh, $stem, $run_id, $text, $mode, $schema_stem) = @_;
    my $pass_fh = anonymous_pass_inode($dir_fh, $text, $mode);
    my @pass_stat = stat($pass_fh);
    @pass_stat && -f _ or die "stage3 shared runner: anonymous PASS identity\n";
    my $pass_identity = {
        dev => $pass_stat[0], ino => $pass_stat[1], sha256 => hash_fh($pass_fh),
    };
    my $prepared_leaf = ".$stem.prepared.$run_id";
    my $prepared_text = join('',
        "schema=$schema_stem-prepared-v1\n", "status=prepared\n",
        "run_id=$run_id\n", "canonical_status=not-published\n",
        "pass_dev=$pass_identity->{dev}\n", "pass_ino=$pass_identity->{ino}\n",
        "pass_sha256=$pass_identity->{sha256}\n");
    my $prepared_identity = publish_exclusive_at(
        $dir_fh, $prepared_leaf, $prepared_text, $mode, 'prepared');
    my $commit_leaf = ".$stem.commit.$run_id";
    my $commit_text = join('',
        "schema=$schema_stem-commit-v1\n", "status=prepared\n",
        "run_id=$run_id\n", "canonical_status=not-published\n",
        "prepared_dev=$prepared_identity->{dev}\n",
        "prepared_ino=$prepared_identity->{ino}\n",
        "prepared_sha256=$prepared_identity->{sha256}\n",
        "pass_dev=$pass_identity->{dev}\n", "pass_ino=$pass_identity->{ino}\n",
        "pass_sha256=$pass_identity->{sha256}\n");
    publish_exclusive_at($dir_fh, $commit_leaf, $commit_text, $mode, 'commit');
    return ($pass_fh, $pass_identity, $prepared_leaf, $commit_leaf);
}
sub open_regular_at {
    my ($dir_fh, $leaf) = @_;
    $leaf =~ /\A[A-Za-z0-9._-]+\z/
        or die "stage3 shared runner: invalid recovery leaf\n";
    my $fd = syscall($SYS_OPENAT, fileno($dir_fh), $leaf,
        O_RDONLY | O_NOFOLLOW | $O_CLOEXEC, 0);
    my $fh = descriptor_handle($fd, "open recovery $leaf");
    my @st = stat($fh);
    @st && -f _ or die "stage3 shared runner: recovery leaf not regular\n";
    return ($fh, { dev => $st[0], ino => $st[1], sha256 => hash_fh($fh) });
}
sub parse_small_receipt_fh {
    my ($fh, $expected) = @_;
    my $text = read_fh_text($fh, 65_536);
    $text =~ /\n\z/ && $text !~ /\0/
        or die "stage3 shared runner: malformed recovery receipt\n";
    my %value;
    my @line = split /\n/, $text, -1;
    @line && pop(@line) eq ''
        or die "stage3 shared runner: recovery receipt terminator\n";
    @line == @$expected
        or die "stage3 shared runner: recovery receipt row count\n";
    for my $index (0 .. $#line) {
        $line[$index] =~ /\A\Q$expected->[$index]\E=(.*)\z/
            or die "stage3 shared runner: malformed recovery row\n";
        $value{$expected->[$index]} = $1;
    }
    return \%value;
}
sub parse_canonical_receipt_fh {
    my ($fh) = @_;
    my $text = read_fh_text($fh, 65_536);
    $text =~ /\n\z/ && $text !~ /\0/
        or die "stage3 shared runner: malformed canonical recovery receipt\n";
    my %value;
    my @line = split /\n/, $text, -1;
    @line && pop(@line) eq ''
        or die "stage3 shared runner: canonical recovery terminator\n";
    @line >= 3 && @line <= 256
        or die "stage3 shared runner: canonical recovery row count\n";
    for my $line (@line) {
        $line =~ /\A([a-z][a-z0-9_]*)=(.*)\z/ && !exists($value{$1})
            or die "stage3 shared runner: malformed canonical recovery row\n";
        $value{$1} = $2;
    }
    return \%value;
}
sub accept_committed_canonical_at {
    my ($dir_fh, $canonical_leaf, $prepared_leaf, $commit_leaf,
        $run_id, $schema_stem) = @_;
    my ($canonical_fh, $canonical_identity) =
        open_regular_at($dir_fh, $canonical_leaf);
    my ($prepared_fh, $prepared_identity) =
        open_regular_at($dir_fh, $prepared_leaf);
    my ($commit_fh) = open_regular_at($dir_fh, $commit_leaf);
    my $canonical = parse_canonical_receipt_fh($canonical_fh);
    my @prepared_order = qw(schema status run_id canonical_status
        pass_dev pass_ino pass_sha256);
    my @commit_order = qw(schema status run_id canonical_status
        prepared_dev prepared_ino prepared_sha256 pass_dev pass_ino pass_sha256);
    my $prepared = parse_small_receipt_fh($prepared_fh, \@prepared_order);
    my $commit = parse_small_receipt_fh($commit_fh, \@commit_order);
    for my $value ($prepared->{pass_dev}, $commit->{prepared_dev},
            $commit->{pass_dev}) {
        $value =~ /\A[0-9]+\z/
            or die "stage3 shared runner: recovery device grammar\n";
    }
    for my $value ($prepared->{pass_ino}, $commit->{prepared_ino},
            $commit->{pass_ino}) {
        $value =~ /\A[1-9][0-9]*\z/
            or die "stage3 shared runner: recovery inode grammar\n";
    }
    for my $value ($prepared->{pass_sha256}, $commit->{prepared_sha256},
            $commit->{pass_sha256}) {
        valid_sha($value)
            or die "stage3 shared runner: recovery hash grammar\n";
    }
    my ($canonical_schema, $canonical_status) =
        $schema_stem eq 'simple-stage3-shared-runner'
        ? ("$schema_stem-receipt-v1", 'component-pass')
        : ("$schema_stem-v1", 'pass');
    $canonical->{schema} eq $canonical_schema &&
        $canonical->{status} eq $canonical_status &&
        $canonical->{run_id} eq $run_id &&
        $prepared->{schema} eq "$schema_stem-prepared-v1" &&
        $prepared->{status} eq 'prepared' && $prepared->{run_id} eq $run_id &&
        $prepared->{canonical_status} eq 'not-published' &&
        $commit->{schema} eq "$schema_stem-commit-v1" &&
        $commit->{status} eq 'prepared' && $commit->{run_id} eq $run_id &&
        $commit->{canonical_status} eq 'not-published' &&
        $commit->{prepared_dev} eq "$prepared_identity->{dev}" &&
        $commit->{prepared_ino} eq "$prepared_identity->{ino}" &&
        $commit->{prepared_sha256} eq $prepared_identity->{sha256} &&
        $prepared->{pass_dev} eq "$canonical_identity->{dev}" &&
        $prepared->{pass_ino} eq "$canonical_identity->{ino}" &&
        $prepared->{pass_sha256} eq $canonical_identity->{sha256} &&
        $commit->{pass_dev} eq "$canonical_identity->{dev}" &&
        $commit->{pass_ino} eq "$canonical_identity->{ino}" &&
        $commit->{pass_sha256} eq $canonical_identity->{sha256}
        or die "stage3 shared runner: canonical PASS recovery mismatch\n";
    close($commit_fh) or die "stage3 shared runner: close recovery commit: $!\n";
    close($prepared_fh) or die "stage3 shared runner: close recovery prepared: $!\n";
    close($canonical_fh) or die "stage3 shared runner: close recovery canonical: $!\n";
    return 1;
}
sub fsync_parent { fsync_dir(dirname($_[0])); }
sub publish_exclusive {
    my ($path, $text, $mode) = @_;
    normalized_absolute($path) or die "stage3 shared runner: invalid publication path\n";
    absolute_dir(dirname($path));
    my $tmp = "$path.tmp.$parent_pid." . int(rand(1_000_000_000));
    sysopen(my $fh, $tmp,
        O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | $O_CLOEXEC, $mode // 0600)
        or die "stage3 shared runner: create $tmp: $!\n";
    set_cloexec($fh);
    my $offset = 0;
    while ($offset < length($text)) {
        my $wrote = syswrite($fh, $text, length($text) - $offset, $offset);
        if (!defined($wrote)) { next if $! == EINTR; die "write $tmp: $!\n"; }
        $wrote > 0 or die "stage3 shared runner: zero write to $tmp\n";
        $offset += $wrote;
    }
    $fh->sync or die "stage3 shared runner: fsync $tmp: $!\n";
    close($fh) or die "stage3 shared runner: close $tmp: $!\n";
    link($tmp, $path) or do {
        my $error = "$!";
        unlink($tmp) or die "stage3 shared runner: rollback $tmp: $!\n";
        fsync_parent($path);
        die "stage3 shared runner: publication collision: $error\n";
    };
    fsync_parent($path);
    unlink($tmp) or die "stage3 shared runner: remove $tmp: $!\n";
    fsync_parent($path);
}
sub parse_receipt {
    my ($path, $max_bytes) = @_;
    my ($fh, $identity) = open_regular($path, undef);
    my @st = stat($fh);
    $st[7] > 0 && $st[7] <= $max_bytes
        or die "stage3 shared runner: receipt size invalid\n";
    local $/;
    my $text = <$fh>;
    defined($text) && length($text) == $st[7] && $text =~ /\n\z/ && $text !~ /\0/
        or die "stage3 shared runner: malformed receipt bytes\n";
    my (%value, @order);
    my @lines = split /\n/, $text, -1;
    @lines && $lines[-1] eq '' or die "stage3 shared runner: receipt lacks newline\n";
    pop @lines;
    for my $line (@lines) {
        length($line) or die "stage3 shared runner: blank receipt row\n";
        $line =~ /\A([a-z][a-z0-9_]*)=(.*)\z/
            or die "stage3 shared runner: malformed receipt row\n";
        !exists($value{$1}) or die "stage3 shared runner: duplicate receipt key\n";
        $value{$1} = $2;
        push @order, $1;
    }
    return ($fh, $identity, \%value, \@order, $text);
}
sub retained_pairs {
    my ($fh, $max_bytes) = @_;
    my $text = read_fh_text($fh, $max_bytes);
    $text =~ /\n\z/ && $text !~ /\0/
        or die "stage3 shared runner: malformed retained pairs\n";
    my %value;
    for my $line (split /\n/, $text) {
        next unless length($line);
        $line =~ /\A([a-z][a-z0-9_]*)=(.*)\z/
            or die "stage3 shared runner: malformed retained pair\n";
        !exists($value{$1})
            or die "stage3 shared runner: duplicate retained pair\n";
        $value{$1} = $2;
    }
    return \%value;
}
sub parse_unit_plan {
    my ($path) = @_;
    my ($fh, $identity) = open_regular($path, undef);
    local $/;
    my $text = <$fh>;
    defined($text) && length($text) <= 16_777_216 && $text =~ /\n\z/
        or die "stage3 shared runner: invalid unit launch plan\n";
    my (%value, %roles, @row_order);
    for my $line (split /\n/, $text) {
        if ($line =~ /\Arole=([a-z][a-z0-9_]*) path=(\/\S*) sha256=([0-9a-f]{64})\z/) {
            !exists($roles{$1}) or die "stage3 shared runner: duplicate unit role\n";
            $roles{$1} = { path => $2, sha256 => $3 };
            push @row_order, "role:$1";
        } elsif ($line =~ /\A([a-z][a-z0-9_]*)=(.*)\z/) {
            !exists($value{$1}) or die "stage3 shared runner: duplicate unit plan key\n";
            $value{$1} = $2;
            push @row_order, $1;
        } else {
            die "stage3 shared runner: malformed unit plan row\n";
        }
    }
    my @expected_keys = qw(schema status architecture run_id phase unit
        memory_max_bytes memory_swap_max_bytes memory_oom_group runtime_max_sec
        exit_type oom_policy kill_mode send_sigkill cgroup_dev cgroup_ino
        systemd_run_sha256 systemctl_sha256 environment_sha256
        payload_argv_sha256);
    my @expected_roles = qw(analyzer bootstrap_script candidate_builder dash env facade gate_helper
        gate_interpreter payload planner provenance_verifier sampler
        session_helper shared_runner transaction_supervisor);
    my @expected_row_order = (@expected_keys, map { "role:$_" } @expected_roles);
    join("\0", @row_order) eq join("\0", @expected_row_order)
        or die "stage3 shared runner: unit launch plan total row order mismatch\n";
    $value{schema} eq 'simple-stage3-unit-launch-plan-v2' &&
        $value{status} eq 'ready' && $value{phase} eq 'stage3' &&
        $value{run_id} eq $o{run_id} && $value{architecture} eq $o{architecture} &&
        $value{unit} =~ /\Asimple-stage3-[0-9a-f]{20}-stage3\z/ &&
        $value{memory_max_bytes} eq '8589934592' &&
        $value{memory_swap_max_bytes} eq '0' && $value{memory_oom_group} eq '1' &&
        $value{runtime_max_sec} eq '3900' && $value{exit_type} eq 'cgroup' &&
        $value{oom_policy} eq 'kill' && $value{kill_mode} eq 'control-group' &&
        $value{send_sigkill} eq 'yes' &&
        $value{cgroup_dev} =~ /\A[0-9]+\z/ &&
        $value{cgroup_ino} =~ /\A[1-9][0-9]*\z/ &&
        $value{systemd_run_sha256} eq $o{systemd_run_sha256} &&
        $value{systemctl_sha256} eq $o{systemctl_sha256}
        or die "stage3 shared runner: unit launch plan policy mismatch\n";
    return ($fh, $identity, \%value, \%roles);
}

for my $key (qw(payload_exec runner_exec root unit_evidence active_cgroup_receipt
        run_id architecture source_output stage2_transaction_root
        compatibility_marker raw descriptor parent_provenance
        parent_provenance_verify source_snapshot git_receipt runtime_snapshot
        tool_snapshot stage2_admission planner_receipt candidate_output
        candidate_provenance facade systemd_run systemd_run_sha256 systemctl
        systemctl_sha256 sampler_exec sampler_sha256 analyzer_exec
        analyzer_sha256 admitted_compiler admitted_compiler_sha256 dash_exec
        dash_sha256 candidate_builder_sha256 runner_sha256
        provenance_verifier_sha256)) {
    defined($o{$key}) && length($o{$key})
        or die "stage3 shared runner: missing --$key\n";
}
valid_run_id($o{run_id}) or die "stage3 shared runner: invalid run id\n";
$o{architecture} =~ /\A(?:x86_64|aarch64|riscv64)-unknown-linux-gnu\z/
    or die "stage3 shared runner: invalid architecture\n";
for my $key (grep { /sha256\z/ } keys %o) {
    valid_sha($o{$key}) or die "stage3 shared runner: invalid hash option\n";
}
for my $key (qw(root unit_evidence active_cgroup_receipt compatibility_marker raw descriptor
        parent_provenance parent_provenance_verify source_snapshot git_receipt
        runtime_snapshot tool_snapshot stage2_admission planner_receipt
        candidate_output candidate_provenance facade systemd_run systemctl
        admitted_compiler)) {
    normalized_absolute($o{$key})
        or die "stage3 shared runner: invalid absolute path option $key\n";
}
$o{source_output} =~ m{\A/} && normalized_absolute($o{source_output}) &&
    $o{source_output} !~ /[\x00-\x1f\x7f]/
    or die "stage3 shared runner: invalid source output\n";
my ($stage2_transaction_fh, $stage2_transaction_identity) =
    procfd_directory($o{stage2_transaction_root}, 'Stage2 transaction root');
$held{stage2_transaction_root} =
    [$stage2_transaction_fh, $stage2_transaction_identity];
absolute_dir($o{root});
absolute_dir($o{unit_evidence});
$unit_evidence_dir_fh = open_directory_walk($o{unit_evidence});

my @environment_keys = qw(HOME TMPDIR PATH LC_ALL LANG RUST_LOG LIBRARY_PATH
    SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256 SIMPLE_BOOTSTRAP
    SIMPLE_NO_DEPRECATED_WARNINGS SIMPLE_STAGE3_STREAMING_SURFACES
    MALLOC_ARENA_MAX MALLOC_TRIM_THRESHOLD_ SIMPLE_NATIVE_ARENA_DECLS
    SIMPLE_NO_STUB_FALLBACK SIMPLE_BUILD_PROGRESS_EVENTS
    SIMPLE_COMPILER_PHASE_PROFILE SIMPLE_COMPILER_PHASE_PROFILE_FILE
    SIMPLE_MEM_SNAPSHOT_FILE SIMPLE_EVIDENCE_RUN_ID
    LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING SIMPLE_NATIVE_BUILD_TARGET
    SIMPLE_NATIVE_BUILD_THREADS SIMPLE_NATIVE_BUILD_CACHE_DIR
    SIMPLE_RUNTIME_PATH SIMPLE_NATIVE_RUNTIME_BUNDLE SIMPLE_BINARY);
my %environment_allowed = map { $_ => 1 } @environment_keys;
for my $key (keys %ENV) {
    exists($environment_allowed{$key})
        or die "stage3 shared runner: unplanned environment key $key\n";
}
for my $key (@environment_keys) {
    exists($ENV{$key}) or die "stage3 shared runner: missing environment key $key\n";
    length($ENV{$key}) || $key eq 'LIBRARY_PATH'
        or die "stage3 shared runner: empty environment value $key\n";
}
$ENV{LC_ALL} eq 'C' && $ENV{LANG} eq 'C' &&
    $ENV{SIMPLE_EVIDENCE_RUN_ID} eq $o{run_id} &&
    $ENV{SIMPLE_NATIVE_BUILD_TARGET} eq $o{architecture} &&
    $ENV{SIMPLE_NATIVE_BUILD_THREADS} eq '1' &&
    $ENV{SIMPLE_NO_STUB_FALLBACK} eq '1' &&
    $ENV{SIMPLE_STAGE3_STREAMING_SURFACES} eq '1' &&
    $ENV{SIMPLE_COMPILER_PHASE_PROFILE} eq '1' &&
    $ENV{SIMPLE_BINARY} eq $o{admitted_compiler}
    or die "stage3 shared runner: environment policy mismatch\n";
for my $path_key (qw(HOME TMPDIR)) {
    absolute_dir($ENV{$path_key});
    my $fh = open_directory_descriptor($ENV{$path_key});
    $held{"environment-directory:$path_key"} = [$fh, directory_identity($fh)];
}
for my $part (split /:/, $ENV{PATH}, -1) { absolute_dir($part); }
normalized_absolute($ENV{SIMPLE_COMPILER_PHASE_PROFILE_FILE}) &&
    normalized_absolute($ENV{SIMPLE_MEM_SNAPSHOT_FILE}) &&
    normalized_absolute($ENV{SIMPLE_NATIVE_BUILD_CACHE_DIR}) &&
    normalized_absolute($ENV{SIMPLE_RUNTIME_PATH})
    or die "stage3 shared runner: environment path mismatch\n";

my $roles_dir = "$o{unit_evidence}/roles";
absolute_dir($roles_dir);
my %identity_path = (
    admitted_compiler => $o{admitted_compiler},
    sampler => "$roles_dir/sampler", analyzer => "$roles_dir/analyzer",
    transaction_supervisor => "$roles_dir/transaction_supervisor",
    shared_runner => "$roles_dir/shared_runner", gate_helper => "$roles_dir/gate_helper",
    dash => "$roles_dir/dash", perl => "$roles_dir/payload",
    session_helper => "$roles_dir/session_helper",
    bootstrap_script => "$roles_dir/bootstrap_script",
    candidate_builder => "$roles_dir/candidate_builder",
    systemd_run => $o{systemd_run}, systemctl => $o{systemctl},
    planner => "$roles_dir/planner",
    provenance_verifier => "$roles_dir/provenance_verifier",
);
my @identity_roles = qw(admitted_compiler sampler analyzer transaction_supervisor
    shared_runner gate_helper dash perl session_helper bootstrap_script
    candidate_builder systemd_run systemctl planner provenance_verifier);

my ($unit_plan_fh, $unit_plan_identity, $unit_plan, $unit_roles) =
    parse_unit_plan("$o{unit_evidence}/launch-plan.env");
$held{unit_plan} = [$unit_plan_fh, $unit_plan_identity];
my %unit_role_identity;
for my $role (sort keys %$unit_roles) {
    my $expected_path = "$roles_dir/$role";
    $unit_roles->{$role}{path} eq $expected_path
        or die "stage3 shared runner: unit role path mismatch for $role\n";
    my ($fh, $identity) = open_regular($expected_path,
        $unit_roles->{$role}{sha256});
    $held{"unit_role:$role"} = [$fh, $identity];
    $unit_role_identity{$role} = $identity;
}
$unit_role_identity{payload}{sha256} eq
        $unit_role_identity{gate_interpreter}{sha256}
    or die "stage3 shared runner: Perl role bytes mismatch\n";
my ($facade_source_fh, $facade_source_identity) = open_regular($o{facade},
    $unit_role_identity{facade}{sha256});
$held{facade_source} = [$facade_source_fh, $facade_source_identity];
my @service_environment = map { "$_=$ENV{$_}" } @environment_keys;
$unit_plan->{environment_sha256} eq vector_hash(@service_environment)
    or die "stage3 shared runner: unit environment vector mismatch\n";
$o{payload_exec} =~ m{\A/proc/[1-9][0-9]*/fd/[0-9]+\z} &&
    $o{runner_exec} =~ m{\A/proc/[1-9][0-9]*/fd/[0-9]+\z} &&
    $0 eq $o{runner_exec}
    or die "stage3 shared runner: payload executable vector mismatch\n";
$unit_plan->{payload_argv_sha256} eq
        vector_hash($o{payload_exec}, $o{runner_exec}, @original_argv)
    or die "stage3 shared runner: unit payload argv vector mismatch\n";

my ($active_cgroup_fh, $active_cgroup_identity, $active_cgroup,
    $active_cgroup_order) = parse_receipt($o{active_cgroup_receipt}, 65_536);
my @active_cgroup_expected = qw(schema architecture run_id phase unit cgroup
    cgroup_dev cgroup_ino);
join("\0", @$active_cgroup_order) eq join("\0", @active_cgroup_expected) &&
    $active_cgroup->{schema} eq 'simple-stage3-active-cgroup-v1' &&
    $active_cgroup->{architecture} eq $o{architecture} &&
    $active_cgroup->{run_id} eq $o{run_id} &&
    $active_cgroup->{phase} eq 'stage3' &&
    $active_cgroup->{unit} eq $unit_plan->{unit} &&
    $active_cgroup->{cgroup} =~ m{\A/[A-Za-z0-9_.:/-]+\z} &&
    $active_cgroup->{cgroup_dev} eq $unit_plan->{cgroup_dev} &&
    $active_cgroup->{cgroup_ino} eq $unit_plan->{cgroup_ino}
    or die "stage3 shared runner: active cgroup receipt mismatch\n";
$held{active_cgroup_receipt} = [$active_cgroup_fh, $active_cgroup_identity];

my %role_identity;
for my $role (@identity_roles) {
    my $expected;
    if ($role eq 'admitted_compiler') { $expected = $o{admitted_compiler_sha256}; }
    elsif ($role eq 'sampler') { $expected = $o{sampler_sha256}; }
    elsif ($role eq 'analyzer') { $expected = $o{analyzer_sha256}; }
    elsif ($role eq 'shared_runner') { $expected = $o{runner_sha256}; }
    elsif ($role eq 'dash') { $expected = $o{dash_sha256}; }
    elsif ($role eq 'candidate_builder') { $expected = $o{candidate_builder_sha256}; }
    elsif ($role eq 'systemd_run') { $expected = $o{systemd_run_sha256}; }
    elsif ($role eq 'systemctl') { $expected = $o{systemctl_sha256}; }
    elsif ($role eq 'provenance_verifier') { $expected = $o{provenance_verifier_sha256}; }
    my ($fh, $identity);
    if ($role eq 'admitted_compiler' || $role eq 'systemd_run' ||
            $role eq 'systemctl') {
        ($fh, $identity) = open_regular($identity_path{$role}, $expected);
        $held{"role:$role"} = [$fh, $identity];
    } else {
        my $unit_role_name = $role eq 'perl' ? 'payload' : $role;
        $identity = $unit_role_identity{$unit_role_name};
        $fh = $held{"unit_role:$unit_role_name"}[0];
        $held{"role:$role"} = [$fh, $identity];
        (!defined($expected) || $identity->{sha256} eq $expected)
            or die "stage3 shared runner: role hash mismatch for $role\n";
    }
    $role_identity{$role} = $identity;
    if ($role ne 'admitted_compiler' && $role ne 'systemd_run' &&
            $role ne 'systemctl') {
        my $unit_role_name = $role eq 'shared_runner' ? 'shared_runner' :
            $role eq 'perl' ? 'payload' : $role;
        exists($unit_roles->{$unit_role_name}) &&
            $unit_roles->{$unit_role_name}{path} eq $identity_path{$role} &&
            $unit_roles->{$unit_role_name}{sha256} eq $identity->{sha256}
            or die "stage3 shared runner: unit role mismatch for $role\n";
    }
}

my ($payload_exec_fh, $payload_exec_identity) = open_exec_reference(
    $o{payload_exec}, "$roles_dir/payload", $unit_role_identity{payload}{sha256});
my ($runner_exec_fh, $runner_exec_identity) = open_exec_reference(
    $o{runner_exec}, "$roles_dir/shared_runner", $o{runner_sha256});
$held{payload_exec} = [$payload_exec_fh, $payload_exec_identity];
$held{runner_exec} = [$runner_exec_fh, $runner_exec_identity];

my ($sampler_exec_fh, $sampler_exec_identity) = open_exec_reference(
    $o{sampler_exec}, $identity_path{sampler}, $o{sampler_sha256});
my ($analyzer_exec_fh, $analyzer_exec_identity) = open_exec_reference(
    $o{analyzer_exec}, $identity_path{analyzer}, $o{analyzer_sha256});
my ($dash_exec_fh, $dash_exec_identity) = open_exec_reference(
    $o{dash_exec}, $identity_path{dash}, $o{dash_sha256});
$held{sampler_exec} = [$sampler_exec_fh, $sampler_exec_identity];
$held{analyzer_exec} = [$analyzer_exec_fh, $analyzer_exec_identity];
$held{dash_exec} = [$dash_exec_fh, $dash_exec_identity];

# Capture every shell helper that the Stage 3 body can transitively source by
# walking from a held root directory descriptor.  Later repository leaf or
# ancestor replacement can change display paths, but cannot change these bytes.
my $root_dir_fh = open_directory_descriptor($o{root});
my %capsule_relative = (
    jobs_policy => 'scripts/bootstrap/bootstrap-build-jobs-policy.shs',
    authority => 'scripts/check/lib/bootstrap-stage3/authority.shs',
    command_snapshot => 'scripts/check/lib/bootstrap-stage3/command-snapshot.shs',
    sanity => 'scripts/check/lib/bootstrap-stage3/sanity.shs',
    manifest_write => 'scripts/check/lib/bootstrap-stage3/manifest-write.shs',
    manifest_verify => 'scripts/check/lib/bootstrap-stage3/manifest-verify.shs',
    self_test => 'scripts/check/lib/bootstrap-stage3/self-test.shs',
    runner_module => 'scripts/check/lib/bootstrap-stage3/runner.shs',
    planner_admission => 'scripts/check/lib/bootstrap-planner-admission-bound.shs',
    candidate_frontend =>
        'scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs',
);
my (%capsule_helper_fh, %capsule_helper_identity);
for my $name (sort keys %capsule_relative) {
    my ($fh, $identity) = open_root_relative($root_dir_fh,
        $capsule_relative{$name});
    $capsule_helper_fh{$name} = $fh;
    $capsule_helper_identity{$name} = $identity;
}
$held{repository_root} = [$root_dir_fh, directory_identity($root_dir_fh)];
$capsule_helper_fh{facade} = $held{'unit_role:facade'}[0];
$capsule_helper_identity{facade} = $unit_role_identity{facade};
$capsule_helper_fh{candidate_builder} = $held{'role:candidate_builder'}[0];
$capsule_helper_identity{candidate_builder} = $role_identity{candidate_builder};
$capsule_helper_fh{bootstrap_script} = $held{'role:bootstrap_script'}[0];
$capsule_helper_identity{bootstrap_script} = $role_identity{bootstrap_script};
my @capsule_helper_order = qw(bootstrap_script candidate_builder jobs_policy facade
    authority command_snapshot sanity manifest_write manifest_verify self_test
    runner_module planner_admission candidate_frontend);
@capsule_helper_order == 13
    or die "stage3 shared runner: helper capsule inventory count\n";
for my $name (@capsule_helper_order) {
    exists($capsule_helper_fh{$name}) && exists($capsule_helper_identity{$name})
        or die "stage3 shared runner: helper capsule inventory incomplete\n";
    $held{"capsule_helper:$name"} =
        [$capsule_helper_fh{$name}, $capsule_helper_identity{$name}];
}

my %artifact_path = (
    descriptor => $o{descriptor}, parent_provenance => $o{parent_provenance},
    parent_provenance_verify => $o{parent_provenance_verify},
    source_snapshot => $o{source_snapshot}, git_receipt => $o{git_receipt},
    runtime_snapshot => $o{runtime_snapshot}, tool_snapshot => $o{tool_snapshot},
    stage2_admission => $o{stage2_admission}, planner_receipt => $o{planner_receipt},
);
my %artifact_identity;
for my $name (sort keys %artifact_path) {
    my ($fh, $identity) = open_regular($artifact_path{$name}, undef);
    $held{"artifact:$name"} = [$fh, $identity];
    $artifact_identity{$name} = $identity;
}

# Stage 2 is an immutable transaction capsule.  The relative names below are
# protocol names, not paths recovered from source_output (which is audit-only).
my $stage2_display = $o{source_output};
my $stage2_base = "output/stage3/$o{architecture}";
my %stage2_relative = (
    stage2 => "output/stage2/$o{architecture}/simple",
    admitted => "$stage2_base/stage2-admitted/simple",
    stage2_admission => "$stage2_base/stage2-admitted/admission.env",
    seed => "$stage2_base/stage2-runtime-authority/simple",
    seed_stamp => "$stage2_base/stage2-runtime-authority/simple.inputs.sha256",
    native_all => "$stage2_base/stage2-runtime-authority/libsimple_native_all.a",
    compiler_backfill => "$stage2_base/stage2-runtime-authority/libsimple_compiler_backfill.a",
    stage2_sanity => "$stage2_base/stage2-sanity.env",
    stage2_receiver => "$stage2_base/stage2-receiver.env",
    stage2_receiver_log => "$stage2_base/stage2-receiver.log",
    stage2_transcript => "$stage2_base/stage2-command.transcript",
    stage2_build_log => "output/logs/$o{architecture}/stage2-native-build.log",
    source_before => "$stage2_base/source-inputs-before.txt",
    git_before => "$stage2_base/git-state-before.env",
    tool_before => "$stage2_base/tool-authority-before.txt",
    runtime_origin_before => "$stage2_base/runtime-origin-before.txt",
    runtime_origin_after => "$stage2_base/runtime-origin-after.txt",
    runtime_admitted => "$stage2_base/runtime-admitted.txt",
);
my (%stage2_input_fh, %stage2_input_identity);
for my $name (sort keys %stage2_relative) {
    next if $name eq 'compiler_backfill';
    my ($fh, $identity) = open_root_relative($stage2_transaction_fh,
        $stage2_relative{$name});
    $identity->{path} = "$stage2_display/$stage2_relative{$name}";
    my @st = stat($fh); $identity->{mode} = $st[2];
    $stage2_input_fh{$name} = $fh;
    $stage2_input_identity{$name} = $identity;
    $held{"stage2:$name"} = [$fh, $identity];
}
{
    my ($fh, $identity) = open_optional_root_relative($stage2_transaction_fh,
        $stage2_relative{compiler_backfill});
    if (defined($fh)) {
    $identity->{path} = "$stage2_display/$stage2_relative{compiler_backfill}";
    my @st = stat($fh); $identity->{mode} = $st[2];
    $stage2_input_fh{compiler_backfill} = $fh;
    $stage2_input_identity{compiler_backfill} = $identity;
        $held{'stage2:compiler_backfill'} = [$fh, $identity];
    } else {
        $stage2_input_identity{compiler_backfill} = {
            path => "$stage2_display/$stage2_relative{compiler_backfill}",
            absent => 1 };
    }
}
for my $spec ([runtime_dir => "$stage2_base/stage2-runtime-authority"],
        [stage2_cache_dir => "$stage2_base/stage2-native-cache"]) {
    my ($name, $relative) = @$spec;
    my ($fh, $identity) = open_relative_directory($stage2_transaction_fh,
        $relative, $stage2_display);
    $stage2_input_fh{$name} = $fh; $stage2_input_identity{$name} = $identity;
    $held{"stage2:$name"} = [$fh, $identity];
}
my $stage3_cache_fh = open_directory_walk($ENV{SIMPLE_NATIVE_BUILD_CACHE_DIR});
$held{stage3_cache_dir} = [$stage3_cache_fh, directory_identity($stage3_cache_fh)];

sub output_leaf_binding {
    my ($name, $path) = @_;
    normalized_absolute($path) or die "stage3 shared runner: invalid output $name\n";
    (-e $path || -l $path) and die "stage3 shared runner: output collision $name\n";
    my $parent_path = dirname($path); my $leaf = basename($path);
    $leaf =~ /\A[A-Za-z0-9_.-]+\z/ or die "stage3 shared runner: unsafe output leaf\n";
    my $parent = open_directory_walk($parent_path);
    my $identity = directory_identity($parent);
    $held{"output-parent:$name"} = [$parent, $identity];
    return parent_fd_path($parent) . "/$leaf";
}

my %builder_output = (
    jobs_receipt => "$o{unit_evidence}/effective-build-jobs.env",
    candidate => $o{candidate_output}, manifest => $o{candidate_provenance},
    stage3_transcript => "$o{unit_evidence}/stage3-command.transcript",
    stage3_log => "$o{unit_evidence}/stage3-build.log",
    stage3_sanity => "$o{unit_evidence}/stage3-sanity.env",
    source_after => "$o{unit_evidence}/source-inputs-after.txt",
    git_after => "$o{unit_evidence}/git-state-after.env",
    tool_after => "$o{unit_evidence}/tool-authority-after.txt",
    progress => $ENV{SIMPLE_BUILD_PROGRESS_EVENTS}, rss_raw => $o{raw},
    result_descriptor_map => "$o{unit_evidence}/result-descriptor-map.env",
);
my %builder_output_leaf;
for my $name (sort keys %builder_output) {
    $builder_output_leaf{$name} = output_leaf_binding($name, $builder_output{$name});
}
my %builder_dir;
for my $entry ([stage3_cache_dir => $ENV{SIMPLE_NATIVE_BUILD_CACHE_DIR}],
        [private_home => $ENV{HOME}], [private_tmp => $ENV{TMPDIR}]) {
    my ($name, $path) = @$entry;
    my $fh = open_directory_walk($path);
    $builder_dir{$name} = $fh;
    $held{"builder-dir:$name"} = [$fh, directory_identity($fh)];
}

my @descriptor_roles = ('root', sort keys %stage2_input_identity,
    qw(stage3_cache_dir private_home private_tmp));
my @descriptor_rows;
my @descriptor_vector;
for my $role (@descriptor_roles) {
    my ($descriptor, $display, $dev, $ino, $mode, $sha);
    if ($role eq 'root') {
        my @st = stat($root_dir_fh);
        ($descriptor, $display, $dev, $ino, $mode, $sha) =
            (parent_fd_path($root_dir_fh), $o{root}, $st[0], $st[1], $st[2], 'identity-only');
    } elsif ($role eq 'stage3_cache_dir' || $role eq 'private_home' || $role eq 'private_tmp') {
        my $fh = $builder_dir{$role}; my @st = stat($fh);
        my $display_name = $role eq 'stage3_cache_dir' ? $ENV{SIMPLE_NATIVE_BUILD_CACHE_DIR} :
            $role eq 'private_home' ? $ENV{HOME} : $ENV{TMPDIR};
        ($descriptor, $display, $dev, $ino, $mode, $sha) =
            (parent_fd_path($fh), $display_name, $st[0], $st[1], $st[2], 'identity-only');
    } elsif ($stage2_input_identity{$role}{absent}) {
        ($descriptor, $display, $dev, $ino, $mode, $sha) =
            ('descriptor-absent', $stage2_input_identity{$role}{path}, ('absent') x 4);
    } else {
        my $fh = $stage2_input_fh{$role}; my @st = stat($fh);
        ($descriptor, $display, $dev, $ino, $mode, $sha) =
            (parent_fd_path($fh), $stage2_input_identity{$role}{path},
             $st[0], $st[1], $st[2], (-d _ ? 'identity-only' : hash_fh($fh)));
    }
    push @descriptor_rows, map { "${role}_$_->[0]=$_->[1]\n" }
        map { [$_->[0], $_->[1]] } [descriptor => $descriptor], [display_token => $display],
            [dev => "$dev"], [ino => "$ino"], [mode => "$mode"], [sha256 => $sha];
    push @descriptor_vector, $role, $descriptor, $display, "$dev", "$ino", "$mode", $sha;
}
my $descriptor_map_path = "$o{unit_evidence}/authority-descriptors.env";
my $descriptor_map_text = join('',
    "schema=simple-stage3-authority-descriptors-v2\n", "status=ready\n",
    "run_id=$o{run_id}\n", "architecture=$o{architecture}\n",
    "descriptor_owner_pid=$parent_pid\n",
    "descriptor_owner_start_ticks=" . proc_start_ticks($parent_pid) . "\n",
    "entry_count=" . scalar(@descriptor_roles) . "\n",
    "map_vector_sha256=" . vector_hash(@descriptor_vector) . "\n",
    @descriptor_rows);
publish_exclusive($descriptor_map_path, $descriptor_map_text, 0600);
my ($descriptor_map_fh, $descriptor_map_identity) =
    open_regular($descriptor_map_path, sha256_hex($descriptor_map_text));
$held{descriptor_map} = [$descriptor_map_fh, $descriptor_map_identity];

my $memory = $ENV{SIMPLE_MEM_SNAPSHOT_FILE};
my $phase = $ENV{SIMPLE_COMPILER_PHASE_PROFILE_FILE};
my $identity_manifest = "$o{unit_evidence}/transitive-identity.events";
my $argv_transcript = "$o{unit_evidence}/argv-transcript.events";
my $env_transcript = "$o{unit_evidence}/environment-transcript.events";
my $launch_plan = "$o{unit_evidence}/stage3-launch-plan.env";
my $analysis_output = "$o{unit_evidence}/analysis";
my $candidate_verify = "$o{unit_evidence}/candidate-provenance-verification.env";
my $console_log = "$o{unit_evidence}/runner-console.log";
my $component_receipt = "$o{unit_evidence}/runner-receipt.env";
my $helper_capsule = "$o{unit_evidence}/stage3-helper-capsule.shs";
my $helper_capsule_inventory =
    "$o{unit_evidence}/stage3-helper-capsule-inventory.env";
my $manifest_bound_map = "$o{unit_evidence}/manifest-bound-artifacts.env";
for my $target ($o{raw}, $memory, $phase, $o{candidate_output},
        $o{candidate_provenance}, $identity_manifest, $argv_transcript,
        $env_transcript, $launch_plan, $analysis_output, $candidate_verify,
        $console_log, $component_receipt, $helper_capsule,
        $helper_capsule_inventory, $manifest_bound_map) {
    normalized_absolute($target) or die "stage3 shared runner: invalid target path\n";
    !-e $target && !-l $target or die "stage3 shared runner: target collision $target\n";
    absolute_dir(dirname($target));
}

my %obsolete_candidate_output_display = (
    rss_raw => $o{raw}, jobs_receipt => dirname($o{candidate_output}) . '/effective-build-jobs.env',
    candidate_output => $o{candidate_output}, candidate_provenance => $o{candidate_provenance},
    stage3_transcript => dirname($o{candidate_output}) . '/stage3-command.transcript',
    stage3_build_log => dirname($o{candidate_output}) . '/stage3-build.log',
    stage3_sanity => dirname($o{candidate_output}) . '/stage3-sanity.env',
    source_after => dirname($o{candidate_output}) . '/source-inputs-after.txt',
    git_after => dirname($o{candidate_output}) . '/git-state-after.env',
    tool_after => dirname($o{candidate_output}) . '/tool-authority.txt',
    progress => $ENV{SIMPLE_BUILD_PROGRESS_EVENTS},
);
my @obsolete_descriptor_roles = qw(stage2 admitted stage2_admission seed seed_stamp native_all
    compiler_backfill stage2_sanity stage2_receiver stage2_receiver_log
    stage2_transcript stage2_build_log source_before git_before tool_before
    runtime_origin_before runtime_origin_after runtime_admitted runtime_dir stage2_cache_dir);
my @obsolete_descriptor_vector;
my $obsolete_descriptor_rows = '';
if (0) { for my $name (@obsolete_descriptor_roles) {
    my $identity = $stage2_input_identity{$name};
    defined($identity) or die "stage3 shared runner: missing descriptor role $name\n";
    if ($identity->{absent}) {
        push @obsolete_descriptor_vector, $name, 'descriptor-absent',
            token_v2($identity->{path}), qw(absent absent absent absent);
        $obsolete_descriptor_rows .= "${name}_descriptor=descriptor-absent\n" .
            "${name}_display_token=" . token_v2($identity->{path}) . "\n" .
            "${name}_dev=absent\n${name}_ino=absent\n${name}_mode=absent\n" .
            "${name}_sha256=absent\n";
        next;
    }
    my $descriptor = '/proc/' . $$ . '/fd/' . fileno($stage2_input_fh{$name});
    my $sha = $identity->{directory} ? 'identity-only' : $identity->{sha256};
    push @obsolete_descriptor_vector, $name, $descriptor, token_v2($identity->{path}),
        "$identity->{dev}", "$identity->{ino}", "$identity->{mode}", $sha;
    $obsolete_descriptor_rows .= "${name}_descriptor=$descriptor\n" .
        "${name}_display_token=" . token_v2($identity->{path}) . "\n" .
        "${name}_dev=$identity->{dev}\n${name}_ino=$identity->{ino}\n" .
        "${name}_mode=$identity->{mode}\n${name}_sha256=$sha\n";
} }
my $obsolete_descriptor_map_text = join('',
    "schema=simple-stage3-candidate-builder-descriptor-map-v2\n", "status=ready\n",
    "run_id=$o{run_id}\n", "architecture=$o{architecture}\n",
    "descriptor_owner_pid=$$\n", "descriptor_owner_start_ticks=" . proc_start_ticks($$) . "\n",
    "entry_count=0\n", "map_vector_sha256=" . vector_hash() . "\n");

my $descriptor_ref = sub {
    my ($fh) = @_;
    return '/proc/' . $parent_pid . '/fd/' . fileno($fh);
};
my $capsule_text = join('',
    "#!/bin/dash\n", "set -eu\n",
    '[ "$#" -ge 1 ] || exit 64' . "\n",
    'capsule_entry=$1; shift' . "\n",
    '[ "$capsule_entry" = stage3 ] || exit 64' . "\n",
    "BOOTSTRAP_STAGE3_CAPSULE_ENTRY=stage3\n",
    "BOOTSTRAP_STAGE3_CAPSULE_LOADED=1\n",
    "BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE=1\n",
    'unset BOOTSTRAP_STAGE3_CAPSULE_CALLER_ORIGIN' . "\n",
    'export BOOTSTRAP_STAGE3_CAPSULE_ENTRY BOOTSTRAP_STAGE3_CAPSULE_LOADED ' .
        'BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE' . "\n",
    'BOOTSTRAP_STAGE3_FACADE_PATH=' .
        $descriptor_ref->($capsule_helper_fh{facade}) . "\n",
    'BOOTSTRAP_STAGE3_BOOTSTRAP_SCRIPT_DESCRIPTOR=' .
        $descriptor_ref->($capsule_helper_fh{bootstrap_script}) . "\n",
    'BOOTSTRAP_STAGE3_CANDIDATE_FRONTEND_DESCRIPTOR=' .
        $descriptor_ref->($capsule_helper_fh{candidate_frontend}) . "\n",
    'BOOTSTRAP_STAGE3_AUTHORITY_DESCRIPTOR=' .
        $descriptor_ref->($capsule_helper_fh{authority}) . "\n",
    'BOOTSTRAP_STAGE3_COMMAND_DESCRIPTOR=' .
        $descriptor_ref->($capsule_helper_fh{command_snapshot}) . "\n",
    'BOOTSTRAP_STAGE3_SANITY_DESCRIPTOR=' .
        $descriptor_ref->($capsule_helper_fh{sanity}) . "\n",
    'BOOTSTRAP_STAGE3_MANIFEST_WRITE_DESCRIPTOR=' .
        $descriptor_ref->($capsule_helper_fh{manifest_write}) . "\n",
    'BOOTSTRAP_STAGE3_MANIFEST_VERIFY_DESCRIPTOR=' .
        $descriptor_ref->($capsule_helper_fh{manifest_verify}) . "\n",
    'BOOTSTRAP_STAGE3_SELF_TEST_DESCRIPTOR=' .
        $descriptor_ref->($capsule_helper_fh{self_test}) . "\n",
    'BOOTSTRAP_STAGE3_RUNNER_DESCRIPTOR=' .
        $descriptor_ref->($capsule_helper_fh{runner_module}) . "\n",
    'export BOOTSTRAP_STAGE3_FACADE_PATH ' .
        'BOOTSTRAP_STAGE3_BOOTSTRAP_SCRIPT_DESCRIPTOR ' .
        'BOOTSTRAP_STAGE3_CANDIDATE_FRONTEND_DESCRIPTOR ' .
        'BOOTSTRAP_STAGE3_AUTHORITY_DESCRIPTOR ' .
        'BOOTSTRAP_STAGE3_COMMAND_DESCRIPTOR ' .
        'BOOTSTRAP_STAGE3_SANITY_DESCRIPTOR ' .
        'BOOTSTRAP_STAGE3_MANIFEST_WRITE_DESCRIPTOR ' .
        'BOOTSTRAP_STAGE3_MANIFEST_VERIFY_DESCRIPTOR ' .
        'BOOTSTRAP_STAGE3_SELF_TEST_DESCRIPTOR ' .
        'BOOTSTRAP_STAGE3_RUNNER_DESCRIPTOR' . "\n",
    '. ' . $descriptor_ref->($capsule_helper_fh{jobs_policy}) . "\n",
    '. ' . $descriptor_ref->($capsule_helper_fh{facade}) . "\n",
    '. ' . $descriptor_ref->($capsule_helper_fh{planner_admission}) . "\n",
    '. ' . $descriptor_ref->($capsule_helper_fh{candidate_frontend}) . "\n",
    '. ' . $descriptor_ref->($capsule_helper_fh{candidate_builder}) . ' "$@"' . "\n",
    'exit $?' . "\n");
publish_exclusive($helper_capsule, $capsule_text, 0500);
my ($helper_capsule_fh, $helper_capsule_identity) =
    open_regular($helper_capsule, sha256_hex($capsule_text));
$held{helper_capsule} = [$helper_capsule_fh, $helper_capsule_identity];
my @capsule_inventory_vector;
my $capsule_inventory_rows = '';
my $capsule_index = 0;
for my $name (@capsule_helper_order) {
    my $identity = $capsule_helper_identity{$name};
    my $descriptor_path = $descriptor_ref->($capsule_helper_fh{$name});
    push @capsule_inventory_vector, $name, $identity->{path},
        $descriptor_path, "$identity->{dev}", "$identity->{ino}",
        $identity->{sha256};
    ++$capsule_index;
    $capsule_inventory_rows .= join('',
        "helper_${capsule_index}_name=$name\n",
        "helper_${capsule_index}_display_path=" . token_v2($identity->{path}) . "\n",
        "helper_${capsule_index}_descriptor_path=$descriptor_path\n",
        "helper_${capsule_index}_dev=$identity->{dev}\n",
        "helper_${capsule_index}_ino=$identity->{ino}\n",
        "helper_${capsule_index}_sha256=$identity->{sha256}\n");
}
my $capsule_inventory_sha256 = vector_hash(@capsule_inventory_vector);
my $capsule_parity_sha256 = vector_hash(
    'simple-stage3-helper-capsule-entry-parity-v1',
    'entry', 'stage3', 'full_entry', 'stage3', 'resume_entry', 'stage3',
    'helper_count', "$capsule_index",
    'inventory_sha256', $capsule_inventory_sha256,
    'capsule_sha256', $helper_capsule_identity->{sha256},
    'full_caller_sha256', $role_identity{bootstrap_script}{sha256},
    'candidate_builder_caller_sha256', $role_identity{candidate_builder}{sha256});
my $capsule_inventory_text = join('',
    "schema=simple-stage3-helper-capsule-v1\n", "status=ready\n",
    "entry=stage3\n", "full_entry=stage3\n", "resume_entry=stage3\n",
    "helper_count=$capsule_index\n",
    "inventory_sha256=$capsule_inventory_sha256\n",
    "capsule_display_path=" . token_v2($helper_capsule) . "\n",
    "capsule_dev=$helper_capsule_identity->{dev}\n",
    "capsule_ino=$helper_capsule_identity->{ino}\n",
    "capsule_sha256=$helper_capsule_identity->{sha256}\n",
    "full_caller_sha256=$role_identity{bootstrap_script}{sha256}\n",
    "candidate_builder_caller_sha256=$role_identity{candidate_builder}{sha256}\n",
    "entry_parity_sha256=$capsule_parity_sha256\n", $capsule_inventory_rows);
publish_exclusive($helper_capsule_inventory, $capsule_inventory_text, 0600);
my ($helper_capsule_inventory_fh, $helper_capsule_inventory_identity) =
    open_regular($helper_capsule_inventory, sha256_hex($capsule_inventory_text));
$held{helper_capsule_inventory} =
    [$helper_capsule_inventory_fh, $helper_capsule_inventory_identity];

my @compiler_argv = (
    $o{admitted_compiler}, 'native-build', '--target', $o{architecture},
    '--backend', 'cranelift', '--runtime-bundle', 'core-c-bootstrap',
    '--threads', '1', '--cache-dir', $ENV{SIMPLE_NATIVE_BUILD_CACHE_DIR},
    '--mode', 'dynload', '--runtime-path', $ENV{SIMPLE_RUNTIME_PATH},
    '-o', $o{candidate_output}, 'src/app/cli/bootstrap_main.spl',
);

my $identity_text = "schema=simple-stage3-transitive-identity-manifest-v1 " .
    "run_id=$o{run_id} seq=0 event=open role=- path_kind=none path=- " .
    "dev=0 ino=0 sha256=- outcome=running\n";
my $identity_seq = 0;
for my $role (@identity_roles) {
    my $identity = $role_identity{$role};
    ++$identity_seq;
    $identity_text .= "schema=simple-stage3-transitive-identity-manifest-v1 " .
        "run_id=$o{run_id} seq=$identity_seq event=identity role=$role " .
        "path_kind=recorded path=" . token_v2($identity->{path}) .
        " dev=$identity->{dev} ino=$identity->{ino} sha256=$identity->{sha256} " .
        "outcome=bound\n";
}
$identity_text .= "schema=simple-stage3-transitive-identity-manifest-v1 " .
    "run_id=$o{run_id} seq=16 event=terminal role=- path_kind=none path=- " .
    "dev=0 ino=0 sha256=- outcome=complete\n";
publish_exclusive($identity_manifest, $identity_text, 0600);
my ($identity_fh, $identity_identity) = open_regular($identity_manifest, undef);
$held{identity_manifest} = [$identity_fh, $identity_identity];

my $argv_text = "schema=simple-stage3-argv-transcript-v1 run_id=$o{run_id} " .
    "seq=0 event=open argc=" . scalar(@compiler_argv) .
    " arg_index=-1 arg_kind=none arg=- outcome=running\n";
for my $index (0 .. $#compiler_argv) {
    my $seq = $index + 1;
    $argv_text .= "schema=simple-stage3-argv-transcript-v1 run_id=$o{run_id} " .
        "seq=$seq event=arg argc=" . scalar(@compiler_argv) .
        " arg_index=$index arg_kind=recorded arg=" . token_v2($compiler_argv[$index]) .
        " outcome=bound\n";
}
my $argv_terminal_seq = @compiler_argv + 1;
$argv_text .= "schema=simple-stage3-argv-transcript-v1 run_id=$o{run_id} " .
    "seq=$argv_terminal_seq event=terminal argc=" . scalar(@compiler_argv) .
    " arg_index=-1 arg_kind=none arg=- outcome=complete\n";
publish_exclusive($argv_transcript, $argv_text, 0600);
my ($argv_fh, $argv_identity) = open_regular($argv_transcript, undef);
$held{argv_transcript} = [$argv_fh, $argv_identity];

my $env_text = "schema=simple-stage3-environment-transcript-v1 run_id=$o{run_id} " .
    "seq=0 event=open count=27 key_kind=none key=- value_kind=none value=- " .
    "outcome=running\n";
for my $index (0 .. $#environment_keys) {
    my $seq = $index + 1;
    my $key = $environment_keys[$index];
    my ($kind, $value) = $key eq 'LIBRARY_PATH' && $ENV{$key} eq ''
        ? ('empty', '-') : ('recorded', token_v2($ENV{$key}));
    $env_text .= "schema=simple-stage3-environment-transcript-v1 run_id=$o{run_id} " .
        "seq=$seq event=env count=27 key_kind=recorded key=$key " .
        "value_kind=$kind value=$value outcome=bound\n";
}
$env_text .= "schema=simple-stage3-environment-transcript-v1 run_id=$o{run_id} " .
    "seq=28 event=terminal count=27 key_kind=none key=- value_kind=none value=- " .
    "outcome=complete\n";
publish_exclusive($env_transcript, $env_text, 0600);
my ($env_fh, $env_identity) = open_regular($env_transcript, undef);
$held{env_transcript} = [$env_fh, $env_identity];

my @plan_rows = (
    ['schema', 'simple-stage3-launch-plan-v1'], ['run_id', $o{run_id}],
    ['platform', $o{architecture}], ['backend', 'cranelift'], ['mode', 'dynload'],
    ['jobs', '1'], ['threads', '1'], ['no_stub_fallback', '1'],
    ['streaming_surfaces', '1'], ['unit_name', $unit_plan->{unit}],
    ['memory_max_bytes', '8589934592'], ['memory_swap_max_bytes', '0'],
    ['oom_policy', 'kill'], ['sample_interval_ms', '5'], ['max_gap_ms', '50'],
    ['max_summed_rss_kib', '8388608'], ['compiler_wall_ms', '3600000'],
    ['transaction_wall_ms', '3900000'], ['max_batches', '1000000'],
    ['max_process_records', '16000000'], ['max_tracked_per_batch', '4096'],
    ['max_raw_bytes', '1073741824'], ['closure_reserve_bytes', '65536'],
    ['closure_reserve_records', '256'], ['term_grace_ms', '5000'],
    ['kill_reap_ms', '10000'],
    ['descriptor_path', token_v2($o{descriptor})],
    ['descriptor_sha256', $artifact_identity{descriptor}{sha256}],
    ['provenance_path', token_v2($o{parent_provenance})],
    ['provenance_sha256', $artifact_identity{parent_provenance}{sha256}],
    ['provenance_verify_receipt_path', token_v2($o{parent_provenance_verify})],
    ['provenance_verify_receipt_sha256', $artifact_identity{parent_provenance_verify}{sha256}],
    ['identity_manifest_path', token_v2($identity_manifest)],
    ['identity_manifest_sha256', $identity_identity->{sha256}],
    ['argv_transcript_path', token_v2($argv_transcript)],
    ['argv_transcript_sha256', $argv_identity->{sha256}],
    ['env_transcript_path', token_v2($env_transcript)],
    ['env_transcript_sha256', $env_identity->{sha256}],
    ['source_snapshot_path', token_v2($o{source_snapshot})],
    ['source_snapshot_sha256', $artifact_identity{source_snapshot}{sha256}],
    ['git_receipt_path', token_v2($o{git_receipt})],
    ['git_receipt_sha256', $artifact_identity{git_receipt}{sha256}],
    ['runtime_snapshot_path', token_v2($o{runtime_snapshot})],
    ['runtime_snapshot_sha256', $artifact_identity{runtime_snapshot}{sha256}],
    ['tool_snapshot_path', token_v2($o{tool_snapshot})],
    ['tool_snapshot_sha256', $artifact_identity{tool_snapshot}{sha256}],
    ['stage2_admission_path', token_v2($o{stage2_admission})],
    ['stage2_admission_sha256', $artifact_identity{stage2_admission}{sha256}],
    ['planner_receipt_path', token_v2($o{planner_receipt})],
    ['planner_receipt_sha256', $artifact_identity{planner_receipt}{sha256}],
    ['cgroup_preflight_receipt_path', token_v2($unit_plan_identity->{path})],
    ['cgroup_preflight_receipt_sha256', $unit_plan_identity->{sha256}],
    ['raw_path', token_v2($o{raw})], ['memory_path', token_v2($memory)],
    ['phase_path', token_v2($phase)],
    ['cache_path', token_v2($ENV{SIMPLE_NATIVE_BUILD_CACHE_DIR})],
    ['runtime_path', token_v2($ENV{SIMPLE_RUNTIME_PATH})],
    ['candidate_output_path', token_v2($o{candidate_output})],
    ['evidence_output_dir', token_v2($analysis_output)], ['status', 'ready'],
);
@plan_rows == 60 or die "stage3 shared runner: internal plan row count\n";
my $plan_text = join('', map { "$_->[0]=$_->[1]\n" } @plan_rows);
publish_exclusive($launch_plan, $plan_text, 0600);
my ($plan_fh, $plan_identity) = open_regular($launch_plan, undef);
read_fh_text($plan_fh, 1_048_576) eq $plan_text
    or die "stage3 shared runner: exact 60-row launch plan mismatch\n";
$held{stage3_plan} = [$plan_fh, $plan_identity];

# The remaining execution and receipt-correlation section is deliberately
# below the immutable prelaunch publications.  A failure from this point may
# leave evidence, but it can never publish the component receipt.

sub proc_start_ticks {
    my ($pid) = @_;
    open(my $fh, '<', "/proc/$pid/stat")
        or die "stage3 shared runner: open process identity: $!\n";
    local $/;
    my $text = <$fh>;
    close($fh) or die "stage3 shared runner: close process identity: $!\n";
    defined($text) or die "stage3 shared runner: empty process identity\n";
    my $right = rindex($text, ')');
    $right >= 0 or die "stage3 shared runner: malformed process identity\n";
    my @field = split / /, substr($text, $right + 2);
    defined($field[19]) && $field[19] =~ /\A[1-9][0-9]*\z/
        or die "stage3 shared runner: malformed process start time\n";
    return $field[19];
}
sub child_status {
    my ($status) = @_;
    return 128 + ($status & 127) if $status & 127;
    return ($status >> 8) & 255;
}
sub establish_child_group {
    my ($pid) = @_;
    setpgrp($pid, $pid) and return;
    return if $! == EACCES || $! == ESRCH;
    die "stage3 shared runner: establish child process group: $!\n";
}
sub group_alive {
    my ($pgid) = @_;
    my $sent = kill(0, -$pgid);
    return 1 if $sent > 0 || $! == EPERM;
    return 0 if $! == ESRCH;
    die "stage3 shared runner: probe child process group: $!\n";
}
sub close_group_after_root {
    my ($pgid) = @_;
    return unless group_alive($pgid);
    kill('TERM', -$pgid);
    my $term_deadline = now_ms() + 5_000;
    while (now_ms() < $term_deadline) {
        return unless group_alive($pgid);
        sleep(0.01);
    }
    kill('KILL', -$pgid);
    my $kill_deadline = now_ms() + 10_000;
    while (now_ms() < $kill_deadline) {
        return unless group_alive($pgid);
        sleep(0.01);
    }
    die "stage3 shared runner: descendant process group survived cleanup\n";
}
sub terminate_child_group {
    my ($pid, $pgid) = @_;
    return unless defined($pid);
    my $observed = waitpid($pid, WNOHANG);
    if ($observed == $pid || ($observed == -1 && $! == ECHILD)) {
        close_group_after_root($pgid) if defined($pgid);
        return;
    }
    $observed == -1 and die "stage3 shared runner: cleanup waitpid: $!\n";
    kill('TERM', -$pgid) if defined($pgid);
    my $term_deadline = now_ms() + 5_000;
    while (now_ms() < $term_deadline) {
        $observed = waitpid($pid, WNOHANG);
        if ($observed == $pid || ($observed == -1 && $! == ECHILD)) {
            close_group_after_root($pgid);
            return;
        }
        $observed == -1 and die "stage3 shared runner: cleanup waitpid: $!\n";
        sleep(0.01);
    }
    kill('KILL', -$pgid) if defined($pgid);
    my $kill_deadline = now_ms() + 10_000;
    while (now_ms() < $kill_deadline) {
        $observed = waitpid($pid, WNOHANG);
        if ($observed == $pid || ($observed == -1 && $! == ECHILD)) {
            close_group_after_root($pgid);
            return;
        }
        $observed == -1 and die "stage3 shared runner: cleanup waitpid: $!\n";
        sleep(0.01);
    }
    die "stage3 shared runner: child cleanup deadline exceeded\n";
}
sub wait_child {
    my ($pid, $pgid, $timeout_ms) = @_;
    my $deadline = now_ms() + $timeout_ms;
    while (now_ms() < $deadline && !length($interrupted)) {
        my $observed = waitpid($pid, WNOHANG);
        if ($observed == $pid) {
            my $status = child_status($?);
            close_group_after_root($pgid);
            return $status;
        }
        die "stage3 shared runner: waitpid failed: $!\n" if $observed == -1;
        sleep(0.01);
    }
    terminate_child_group($pid, $pgid);
    die(length($interrupted)
        ? "stage3 shared runner: interrupted by $interrupted\n"
        : "stage3 shared runner: child timeout\n");
}
sub exec_fd_path {
    my ($fh) = @_;
    return '/proc/self/fd/' . fileno($fh);
}
sub parent_fd_path {
    my ($fh) = @_;
    return "/proc/$parent_pid/fd/" . fileno($fh);
}
sub open_console {
    sysopen($console_fh, $console_log,
        O_WRONLY | O_CREAT | O_EXCL | O_APPEND | O_NOFOLLOW | $O_CLOEXEC, 0600)
        or die "stage3 shared runner: create console log: $!\n";
    set_cloexec($console_fh);
}
sub redirect_console {
    open(STDOUT, '>&', $console_fh) or POSIX::_exit(125);
    open(STDERR, '>&', $console_fh) or POSIX::_exit(125);
}
sub run_bound_child {
    my ($exec_fh, $timeout_ms, @argv) = @_;
    my $pid = fork();
    defined($pid) or die "stage3 shared runner: fork child: $!\n";
    if (!$pid) {
        $SIG{HUP} = $SIG{INT} = $SIG{QUIT} = $SIG{TERM} = $SIG{CHLD} = 'DEFAULT';
        setpgrp(0, 0) or POSIX::_exit(125);
        redirect_console();
        my $path = exec_fd_path($exec_fh);
        exec {$path} @argv;
        POSIX::_exit(126);
    }
    establish_child_group($pid);
    $active_pid = $pid;
    $active_pgid = $pid;
    my $status = wait_child($pid, $pid, $timeout_ms);
    undef $active_pid;
    undef $active_pgid;
    return $status;
}
sub fail_if_interrupted {
    my ($boundary) = @_;
    length($interrupted)
        and die "stage3 shared runner: interrupted by $interrupted at $boundary\n";
}
sub begin_canonical_pass_commit {
    # This mask transition is the PASS/signal linearization point.  A signal
    # delivered before it is recorded by the handler; a signal already queued
    # at the transition is observed through sigpending.  Signals arriving after
    # the clean snapshot are ordered after the no-replace PASS commit and remain
    # blocked through _exit.
    my $old_set = POSIX::SigSet->new();
    defined(sigprocmask(SIG_BLOCK, $terminal_signal_set, $old_set))
        or die "stage3 shared runner: block terminal signals: $!\n";
    my $pending = POSIX::SigSet->new();
    defined(sigpending($pending))
        or die "stage3 shared runner: read pending terminal signals: $!\n";
    my @pending_name;
    push @pending_name, 'TERM' if $pending->ismember(SIGTERM);
    push @pending_name, 'INT' if $pending->ismember(SIGINT);
    push @pending_name, 'HUP' if $pending->ismember(SIGHUP);
    push @pending_name, 'QUIT' if $pending->ismember(SIGQUIT);
    if (length($interrupted) || @pending_name) {
        my $signal = length($interrupted) ? $interrupted : $pending_name[0];
        die "stage3 shared runner: interrupted by $signal before canonical PASS commit\n";
    }
}
sub semantic_environment_hash {
    my $sha = Digest::SHA->new(256);
    for my $key (@environment_keys) {
        my $value = $ENV{$key};
        $sha->add(pack('Q>', length($key)), $key,
            pack('Q>', length($value)), $value);
    }
    return $sha->hexdigest;
}
sub semantic_argv_hash {
    my $sha = Digest::SHA->new(256);
    for my $arg (@compiler_argv) {
        $sha->add(pack('Q>', length($arg)), $arg);
    }
    return $sha->hexdigest;
}
sub identity_of_path {
    my ($path) = @_;
    my ($fh, $identity) = open_regular($path, undef);
    close($fh) or die "stage3 shared runner: close identity target: $!\n";
    return $identity;
}
sub durable_identity_of_path {
    my ($path) = @_;
    my ($fh, $identity) = open_regular($path, undef);
    $fh->sync or die "stage3 shared runner: fsync result $path: $!\n";
    stable_identity($fh, $identity)
        or die "stage3 shared runner: result changed during fsync\n";
    close($fh) or die "stage3 shared runner: close result $path: $!\n";
    fsync_parent($path);
    return $identity;
}
sub validate_verification_text {
    my ($text, $provenance_identity, $candidate_identity) = @_;
    my @expected = qw(schema run_id provenance_sha256 candidate_sha256
        source_snapshot_sha256 runtime_snapshot_sha256 tool_snapshot_sha256
        git_receipt_sha256 verifier_sha256 status);
    my @line = split /\n/, $text, -1;
    @line == 11 && $line[-1] eq ''
        or die "stage3 shared runner: verification receipt row count\n";
    pop @line;
    my %value;
    for my $index (0 .. $#expected) {
        $line[$index] =~ /\A\Q$expected[$index]\E=(.*)\z/
            or die "stage3 shared runner: verification receipt order\n";
        $value{$expected[$index]} = $1;
    }
    $value{schema} eq 'simple-stage3-provenance-verification-v1' &&
        $value{run_id} eq $o{run_id} && $value{status} eq 'pass' &&
        $value{provenance_sha256} eq $provenance_identity->{sha256} &&
        $value{candidate_sha256} eq $candidate_identity->{sha256} &&
        $value{source_snapshot_sha256} eq $artifact_identity{source_snapshot}{sha256} &&
        $value{runtime_snapshot_sha256} eq $artifact_identity{runtime_snapshot}{sha256} &&
        $value{tool_snapshot_sha256} eq $artifact_identity{tool_snapshot}{sha256} &&
        $value{git_receipt_sha256} eq $artifact_identity{git_receipt}{sha256} &&
        $value{verifier_sha256} eq $o{provenance_verifier_sha256}
        or die "stage3 shared runner: verification receipt correlation\n";
}
sub validate_parent_authentication_text {
    my ($text, $parent_identity, $candidate_identity) = @_;
    my @expected = qw(schema status run_id architecture parent_v1_sha256
        candidate_sha256 source_snapshot_sha256 runtime_snapshot_sha256
        tool_snapshot_sha256 git_receipt_sha256 stage2_admission_sha256);
    my @line = split /\n/, $text, -1;
    @line == @expected + 1 && $line[-1] eq ''
        or die "stage3 shared runner: parent authentication row count\n";
    pop @line;
    my %value;
    for my $index (0 .. $#expected) {
        $line[$index] =~ /\A\Q$expected[$index]\E=(.*)\z/
            or die "stage3 shared runner: parent authentication order\n";
        $value{$expected[$index]} = $1;
    }
    $value{schema} eq 'simple-stage23-parent-v1-authentication-v1' &&
        $value{status} eq 'pass' && $value{run_id} eq $o{run_id} &&
        $value{architecture} eq $o{architecture} &&
        $value{parent_v1_sha256} eq $parent_identity->{sha256} &&
        $value{candidate_sha256} eq $candidate_identity->{sha256} &&
        $value{source_snapshot_sha256} eq
            $artifact_identity{source_snapshot}{sha256} &&
        $value{runtime_snapshot_sha256} eq
            $artifact_identity{runtime_snapshot}{sha256} &&
        $value{tool_snapshot_sha256} eq
            $artifact_identity{tool_snapshot}{sha256} &&
        $value{git_receipt_sha256} eq $artifact_identity{git_receipt}{sha256} &&
        $value{stage2_admission_sha256} eq
            $artifact_identity{stage2_admission}{sha256}
        or die "stage3 shared runner: parent authentication correlation\n";
}
sub capture_verifier {
    my ($provenance_identity, $candidate_identity) = @_;
    my $capture = "$o{unit_evidence}/.candidate-verification.capture.$parent_pid";
    sysopen(my $capture_fh, $capture,
        O_RDWR | O_CREAT | O_EXCL | O_NOFOLLOW | $O_CLOEXEC, 0600)
        or die "stage3 shared runner: create verifier capture: $!\n";
    set_cloexec($capture_fh);
    my $pid = fork();
    defined($pid) or die "stage3 shared runner: fork verifier: $!\n";
    if (!$pid) {
        $SIG{HUP} = $SIG{INT} = $SIG{QUIT} = $SIG{TERM} = $SIG{CHLD} = 'DEFAULT';
        setpgrp(0, 0) or POSIX::_exit(125);
        open(STDOUT, '>&', $capture_fh) or POSIX::_exit(125);
        open(STDERR, '>&', $console_fh) or POSIX::_exit(125);
        my $dash = exec_fd_path($dash_exec_fh);
        exec {$dash} 'dash', parent_fd_path($held{'role:provenance_verifier'}[0]),
            "--run-id=$o{run_id}",
            "--manifest=" . parent_fd_path($held{candidate_provenance}[0]),
            "--manifest-display=$o{candidate_provenance}",
            "--manifest-root-display=" . dirname($o{candidate_provenance}),
            "--bound-artifacts-descriptor=" .
                parent_fd_path($held{manifest_bound_map}[0]),
            "--scratch-root=" .
                parent_fd_path($held{verifier_scratch_root}[0]),
            "--root=$o{root}",
            "--candidate=" . parent_fd_path($held{candidate_output}[0]),
            "--candidate-display=$o{candidate_output}",
            "--source-snapshot=" . parent_fd_path($held{'artifact:source_snapshot'}[0]),
            "--runtime-snapshot=" . parent_fd_path($held{'artifact:runtime_snapshot'}[0]),
            "--tool-snapshot=" . parent_fd_path($held{'artifact:tool_snapshot'}[0]),
            "--git-receipt=" . parent_fd_path($held{'artifact:git_receipt'}[0]),
            "--verifier-sha256=$o{provenance_verifier_sha256}",
            "--facade=" . parent_fd_path($capsule_helper_fh{facade}),
            "--facade-display=$o{facade}",
            "--bootstrap-script-descriptor=" .
                parent_fd_path($capsule_helper_fh{bootstrap_script}),
            "--candidate-frontend-descriptor=" .
                parent_fd_path($capsule_helper_fh{candidate_frontend}),
            "--authority-descriptor=" .
                parent_fd_path($capsule_helper_fh{authority}),
            "--command-descriptor=" .
                parent_fd_path($capsule_helper_fh{command_snapshot}),
            "--sanity-descriptor=" .
                parent_fd_path($capsule_helper_fh{sanity}),
            "--manifest-write-descriptor=" .
                parent_fd_path($capsule_helper_fh{manifest_write}),
            "--manifest-verify-descriptor=" .
                parent_fd_path($capsule_helper_fh{manifest_verify}),
            "--self-test-descriptor=" .
                parent_fd_path($capsule_helper_fh{self_test}),
            "--runner-descriptor=" .
                parent_fd_path($capsule_helper_fh{runner_module}),
            "--launch-plan=" . parent_fd_path($held{stage3_plan}[0]),
            "--launch-plan-sha256=$plan_identity->{sha256}",
            "--memory=" . parent_fd_path($held{memory_result}[0]),
            "--memory-display=$memory",
            "--phase=" . parent_fd_path($held{phase_result}[0]),
            "--phase-display=$phase",
            "--admitted-compiler=" .
                parent_fd_path($held{'role:admitted_compiler'}[0]),
            "--admitted-compiler-display=$o{admitted_compiler}",
            "--stage3-transcript-descriptor=" .
                parent_fd_path($held{stage3_transcript}[0]),
            "--stage3-transcript-display=" .
                $held{stage3_transcript}[1]{path},
            "--helper-capsule-inventory=" .
                parent_fd_path($helper_capsule_inventory_fh),
            "--helper-capsule-inventory-sha256=" .
                $helper_capsule_inventory_identity->{sha256},
            "--helper-capsule-entry-parity-sha256=$capsule_parity_sha256";
        POSIX::_exit(126);
    }
    establish_child_group($pid);
    $active_pid = $pid;
    $active_pgid = $pid;
    my $status = wait_child($pid, $pid, 120_000);
    undef $active_pid;
    undef $active_pgid;
    $status == 0 or die "stage3 shared runner: provenance verifier failed ($status)\n";
    $capture_fh->sync or die "stage3 shared runner: fsync verifier capture: $!\n";
    seek($capture_fh, 0, 0) or die "stage3 shared runner: rewind verifier capture: $!\n";
    local $/;
    my $text = <$capture_fh>;
    defined($text) && length($text) <= 1_048_576
        or die "stage3 shared runner: verifier output cap\n";
    close($capture_fh) or die "stage3 shared runner: close verifier capture: $!\n";
    validate_verification_text($text, $provenance_identity, $candidate_identity);
    publish_exclusive($candidate_verify, $text, 0600);
    unlink($capture) or die "stage3 shared runner: remove verifier capture: $!\n";
    fsync_parent($capture);
}

$SIG{TERM} = sub { $interrupted ||= 'TERM'; kill('TERM', -$active_pgid) if $active_pgid; };
$SIG{INT} = sub { $interrupted ||= 'INT'; kill('TERM', -$active_pgid) if $active_pgid; };
$SIG{HUP} = sub { $interrupted ||= 'HUP'; kill('TERM', -$active_pgid) if $active_pgid; };
$SIG{QUIT} = sub { $interrupted ||= 'QUIT'; kill('TERM', -$active_pgid) if $active_pgid; };

END {
    if ($$ == $parent_pid) {
        my $pid = defined($candidate_builder_pid) ? $candidate_builder_pid : $active_pid;
        my $pgid = defined($active_pgid) ? $active_pgid : $pid;
        if (defined($pid)) {
            my $ok = eval { terminate_child_group($pid, $pgid); 1 };
            warn "stage3 shared runner: exceptional child cleanup failed: $@" unless $ok;
        }
        if (defined($console_fh)) {
            eval { $console_fh->sync; close($console_fh); };
        }
    }
}

open_console();

# The admitted-parent receipt is part of the prelaunch plan, not opaque
# baggage.  Bind it to the admitted compiler and the same frozen verifier and
# source/runtime/tool/Git identities before the compatibility marker can be
# created or any compiler descendant can execute.
validate_parent_authentication_text(
    read_fh_text($held{'artifact:parent_provenance_verify'}[0], 1_048_576),
    $artifact_identity{parent_provenance}, $role_identity{admitted_compiler});

(-e $o{compatibility_marker} || -l $o{compatibility_marker})
    and die "stage3 shared runner: compatibility marker collision\n";
mkdir($o{compatibility_marker}, 0700)
    or die "stage3 shared runner: create compatibility marker: $!\n";
fsync_parent($o{compatibility_marker});
my @marker_stat = lstat($o{compatibility_marker});
@marker_stat && -d _ && !-l _
    or die "stage3 shared runner: compatibility marker identity\n";

pipe(my $candidate_builder_gate_r, my $candidate_builder_gate_w)
    or die "stage3 shared runner: create resume gate: $!\n";
set_cloexec($candidate_builder_gate_r); set_cloexec($candidate_builder_gate_w);
$candidate_builder_pid = fork();
defined($candidate_builder_pid) or die "stage3 shared runner: fork candidate builder: $!\n";
if (!$candidate_builder_pid) {
    $SIG{HUP} = $SIG{INT} = $SIG{QUIT} = $SIG{TERM} = $SIG{CHLD} = 'DEFAULT';
    close($candidate_builder_gate_w);
    my $byte = '';
    while (length($byte) < 1) {
        my $read = sysread($candidate_builder_gate_r, $byte, 1 - length($byte), length($byte));
        if (!defined($read)) { next if $! == EINTR; POSIX::_exit(125); }
        $read > 0 or POSIX::_exit(125);
    }
    close($candidate_builder_gate_r);
    $byte eq 'G' or POSIX::_exit(125);
    setpgrp(0, 0) or POSIX::_exit(125);
    redirect_console();
    my $dash = exec_fd_path($dash_exec_fh);
    my @root_st = stat($root_dir_fh);
    exec {$dash} 'dash', parent_fd_path($helper_capsule_fh), 'stage3',
        '--jobs=1', '--supervised-stage3', "--platform=$o{architecture}",
        "--repository-root=$o{root}", "--root-dir=" . parent_fd_path($root_dir_fh),
        "--root-dev=$root_st[0]", "--root-ino=$root_st[1]",
        "--source-output-display=$o{source_output}", "--evidence-run-id=$o{run_id}",
        "--rss-raw=$builder_output_leaf{rss_raw}",
        "--rss-sampler=" . parent_fd_path($sampler_exec_fh),
        "--rss-sampler-sha256=$o{sampler_sha256}",
        "--admitted-compiler=$o{admitted_compiler}",
        "--admitted-compiler-sha256=$o{admitted_compiler_sha256}",
        "--compatibility-marker=$o{compatibility_marker}",
        "--runner-plan=$launch_plan", "--runner-plan-sha256=$plan_identity->{sha256}",
        "--env-tool=" . parent_fd_path($held{'role:env'}[0]),
        "--planner-admission=$o{planner_receipt}",
        map({ "--$_=" . parent_fd_path($stage2_input_fh{$_}) }
            qw(stage2 stage2_admission seed seed_stamp native_all)),
        "--compiler-backfill=" . ($stage2_input_fh{compiler_backfill}
            ? parent_fd_path($stage2_input_fh{compiler_backfill}) : 'absent'),
        map({ "--$_=" . parent_fd_path($stage2_input_fh{$_}) }
            qw(stage2_sanity stage2_receiver stage2_receiver_log stage2_transcript
               stage2_build_log source_before git_before tool_before
               runtime_origin_before runtime_origin_after runtime_admitted
               stage2_cache_dir)),
        "--stage3-cache-dir=" . parent_fd_path($builder_dir{stage3_cache_dir}),
        "--runtime-dir=" . parent_fd_path($stage2_input_fh{runtime_dir}),
        "--private-home=" . parent_fd_path($builder_dir{private_home}),
        "--private-tmp=" . parent_fd_path($builder_dir{private_tmp}),
        "--jobs-receipt=$builder_output_leaf{jobs_receipt}",
        "--candidate-output=$builder_output_leaf{candidate}",
        "--candidate-provenance=$builder_output_leaf{manifest}",
        "--stage3-transcript=$builder_output_leaf{stage3_transcript}",
        "--stage3-build-log=$builder_output_leaf{stage3_log}",
        "--stage3-sanity=$builder_output_leaf{stage3_sanity}",
        "--source-after=$builder_output_leaf{source_after}",
        "--git-after=$builder_output_leaf{git_after}",
        "--tool-after=$builder_output_leaf{tool_after}",
        "--progress=$builder_output_leaf{progress}",
        "--descriptor-map=" . parent_fd_path($descriptor_map_fh),
        "--descriptor-map-sha256=$descriptor_map_identity->{sha256}",
        "--stage3-display-root=" . dirname($o{candidate_output}),
        "--result-descriptor-map=$builder_output_leaf{result_descriptor_map}";
    POSIX::_exit(126);
}
close($candidate_builder_gate_r);
establish_child_group($candidate_builder_pid);
$active_pid = $candidate_builder_pid;
$active_pgid = $candidate_builder_pid;
my $candidate_builder_start = proc_start_ticks($candidate_builder_pid);
my $pid_text = "$candidate_builder_pid\n";
publish_exclusive("$o{compatibility_marker}/pid", $pid_text, 0600);
my $marker_text = join('',
    "schema=simple-stage3-lock-compatibility-v1\n", "authority=false\n",
    "run_id=$o{run_id}\n", "lock_path=$o{compatibility_marker}\n",
    "lock_dev=$marker_stat[0]\n", "lock_ino=$marker_stat[1]\n",
    "owner_pid=$candidate_builder_pid\n", "owner_start_ticks=$candidate_builder_start\n",
    "runner_dev=$role_identity{shared_runner}{dev}\n",
    "runner_ino=$role_identity{shared_runner}{ino}\n",
    "runner_sha256=$role_identity{shared_runner}{sha256}\n",
    "unit_launch_plan_sha256=$unit_plan_identity->{sha256}\n",
    "stage3_launch_plan_sha256=$plan_identity->{sha256}\n", "status=held\n");
publish_exclusive("$o{compatibility_marker}/compatibility.env", $marker_text, 0600);
fsync_dir($o{compatibility_marker});
print {$candidate_builder_gate_w} 'G' or die "stage3 shared runner: release resume gate: $!\n";
close($candidate_builder_gate_w) or die "stage3 shared runner: close resume gate: $!\n";
my $candidate_builder_status = wait_child($candidate_builder_pid, $candidate_builder_pid, 3_750_000);
undef $candidate_builder_pid;
undef $active_pid;
undef $active_pgid;
$candidate_builder_status == 0 or die "stage3 shared runner: candidate builder failed ($candidate_builder_status)\n";

for my $required ($o{raw}, $memory, $phase, $o{candidate_output},
        $o{candidate_provenance}) {
    -f $required && !-l $required
        or die "stage3 shared runner: required result absent\n";
}
my $candidate_identity = durable_identity_of_path($o{candidate_output});
my $candidate_provenance_identity = durable_identity_of_path($o{candidate_provenance});
($candidate_identity->{dev} != $role_identity{admitted_compiler}{dev} ||
    $candidate_identity->{ino} != $role_identity{admitted_compiler}{ino})
    or die "stage3 shared runner: produced candidate aliases admitted compiler\n";
my ($candidate_hold_fh, $candidate_hold_identity) = open_regular(
    $o{candidate_output}, $candidate_identity->{sha256});
my ($candidate_provenance_hold_fh, $candidate_provenance_hold_identity) =
    open_regular($o{candidate_provenance}, $candidate_provenance_identity->{sha256});
$held{candidate_output} = [$candidate_hold_fh, $candidate_hold_identity];
$held{candidate_provenance} =
    [$candidate_provenance_hold_fh, $candidate_provenance_hold_identity];
my $candidate_manifest = retained_pairs($candidate_provenance_hold_fh, 16_777_216);
my @manifest_bound_pairs = (
    [qw(seed_path seed_sha256)], [qw(native_all_path native_all_sha256)],
    [qw(stage2_path stage2_sha256)],
    [qw(stage2_admitted_path stage2_admitted_sha256)],
    [qw(stage2_build_log_path stage2_build_log_sha256)],
    [qw(stage2_command_transcript_path stage2_command_transcript_sha256)],
    [qw(stage2_sanity_evidence_path stage2_sanity_evidence_sha256)],
    [qw(stage2_receiver_evidence_path stage2_receiver_evidence_sha256)],
    [qw(stage2_admission_receipt_path stage2_admission_receipt_sha256)],
    [qw(stage3_build_log_path stage3_build_log_sha256)],
    [qw(stage3_command_transcript_path stage3_command_transcript_sha256)],
    [qw(stage3_sanity_evidence_path stage3_sanity_evidence_sha256)],
    [qw(git_state_path git_state_sha256)],
    [qw(runtime_origin_snapshot_path runtime_origin_snapshot_sha256)],
    [qw(runtime_admitted_snapshot_path runtime_admitted_snapshot_sha256)],
    [qw(tool_authority_path tool_authority_sha256)],
    [qw(seed_inputs_stamp_path seed_inputs_stamp_sha256)],
    [qw(source_snapshot_path source_snapshot_sha256)],
    [qw(stage3_jobs_receipt_path stage3_jobs_receipt_sha256)]);
my $compiler_backfill_status = $candidate_manifest->{compiler_backfill_status};
defined($compiler_backfill_status)
    or die "stage3 shared runner: missing compiler backfill status\n";
if ($compiler_backfill_status eq 'present') {
    push @manifest_bound_pairs,
        [qw(compiler_backfill_path compiler_backfill_sha256)];
} elsif ($compiler_backfill_status ne 'absent') {
    die "stage3 shared runner: invalid compiler backfill status\n";
}
for my $pair (@manifest_bound_pairs) {
    my ($path_key, $sha_key) = @$pair;
    defined($candidate_manifest->{$path_key}) &&
        defined($candidate_manifest->{$sha_key})
        or die "stage3 shared runner: missing manifest-bound artifact $path_key/$sha_key\n";
    my ($fh, $identity) = open_regular($candidate_manifest->{$path_key},
        $candidate_manifest->{$sha_key});
    $held{"manifest:$path_key"} = [$fh, $identity];
}
for my $directory_key (qw(stage2_native_cache_dir stage3_native_cache_dir
        runtime_path)) {
    my $path = $candidate_manifest->{$directory_key};
    defined($path) && normalized_absolute($path)
        or die "stage3 shared runner: missing manifest-bound directory $directory_key\n";
    my $fh = open_directory_descriptor($path);
    $held{"manifest-directory:$directory_key"} =
        [$fh, directory_identity($fh)];
}
my $manifest_root = dirname($o{candidate_provenance});
for my $extra ([stage2_receiver_log => "$manifest_root/stage2-receiver.log"],
        [source_inputs_before => "$manifest_root/source-inputs-before.txt"],
        [tool_authority_before => "$manifest_root/tool-authority-before.txt"]) {
    my ($name, $path) = @$extra;
    my ($fh, $identity) = open_regular($path, undef);
    $held{"manifest:$name"} = [$fh, $identity];
}
my $bound_map_text = "schema=simple-stage3-bound-artifact-descriptors-v1\n";
for my $pair (@manifest_bound_pairs) {
    my ($path_key) = @$pair;
    $bound_map_text .= "${path_key}=" .
        parent_fd_path($held{"manifest:$path_key"}[0]) . "\n";
}
$bound_map_text .= "compiler_backfill_path=descriptor-absent\n"
    if $compiler_backfill_status eq 'absent';
$bound_map_text .= "stage2_receiver_log=" .
    parent_fd_path($held{'manifest:stage2_receiver_log'}[0]) . "\n";
$bound_map_text .= "source_inputs_before=" .
    parent_fd_path($held{'manifest:source_inputs_before'}[0]) . "\n";
$bound_map_text .= "tool_authority_before=" .
    parent_fd_path($held{'manifest:tool_authority_before'}[0]) . "\n";
$bound_map_text .= "output_path=" . parent_fd_path($held{candidate_output}[0]) . "\n";
for my $directory_key (qw(stage2_native_cache_dir stage3_native_cache_dir
        runtime_path)) {
    $bound_map_text .= "${directory_key}=" . parent_fd_path(
        $held{"manifest-directory:$directory_key"}[0]) . "\n";
}
$bound_map_text .= "replay_home=" . parent_fd_path(
    $held{'environment-directory:HOME'}[0]) . "\n";
$bound_map_text .= "replay_tmpdir=" . parent_fd_path(
    $held{'environment-directory:TMPDIR'}[0]) . "\n";
publish_exclusive($manifest_bound_map, $bound_map_text, 0400);
my ($bound_map_fh, $bound_map_identity) = open_regular($manifest_bound_map,
    sha256_hex($bound_map_text));
$held{manifest_bound_map} = [$bound_map_fh, $bound_map_identity];
$held{stage3_transcript} = $held{'manifest:stage3_command_transcript_path'};

my ($raw_fh, $raw_identity) = open_regular($o{raw}, undef);
my ($memory_fh, $memory_identity) = open_regular($memory, undef);
my ($phase_fh, $phase_identity) = open_regular($phase, undef);
$held{raw_result} = [$raw_fh, $raw_identity];
$held{memory_result} = [$memory_fh, $memory_identity];
$held{phase_result} = [$phase_fh, $phase_identity];

$verifier_scratch_parent =
    "$o{root}/.stage3-verifier-scratch-$o{run_id}-$parent_pid";
$verifier_scratch_path = "$verifier_scratch_parent/root";
mkdir($verifier_scratch_parent, 0700)
    or die "stage3 shared runner: create verifier scratch parent: $!\n";
mkdir($verifier_scratch_path, 0700)
    or die "stage3 shared runner: create verifier scratch root: $!\n";
my @scratch_stat = lstat($verifier_scratch_path);
@scratch_stat && S_ISDIR($scratch_stat[2]) &&
    ($scratch_stat[2] & 07777) == 0700 && $scratch_stat[4] == $<
    or die "stage3 shared runner: invalid verifier scratch root\n";
my $verifier_scratch_fh = open_directory_descriptor($verifier_scratch_path);
$held{verifier_scratch_root} =
    [$verifier_scratch_fh, directory_identity($verifier_scratch_fh)];

my $verifier_ok = eval {
    capture_verifier($candidate_provenance_identity, $candidate_identity);
    1;
};
my $verifier_error = $@;
my $scratch_root_removed = rmdir($verifier_scratch_path);
my $scratch_root_error = "$!";
my $scratch_parent_removed = $scratch_root_removed &&
    rmdir($verifier_scratch_parent);
my $scratch_parent_error = "$!";
$verifier_ok or die $verifier_error;
$scratch_root_removed
    or die "stage3 shared runner: verifier scratch root not empty: $scratch_root_error\n";
$scratch_parent_removed
    or die "stage3 shared runner: verifier scratch parent not empty: $scratch_parent_error\n";
my ($candidate_verify_fh, $candidate_verify_identity) =
    open_regular($candidate_verify, undef);
$held{candidate_verify} = [$candidate_verify_fh, $candidate_verify_identity];

my @analyzer_argv = (
    $identity_path{analyzer}, 'analyze', '--samples',
    parent_fd_path($held{raw_result}[0]), '--memory',
    parent_fd_path($held{memory_result}[0]), '--phase',
    parent_fd_path($held{phase_result}[0]), '--descriptor',
    parent_fd_path($held{'artifact:descriptor'}[0]), '--provenance',
    parent_fd_path($held{'artifact:parent_provenance'}[0]), '--launch-plan',
    parent_fd_path($held{stage3_plan}[0]),
    '--run-id', $o{run_id}, '--analyzer-sha256', $o{analyzer_sha256},
    '--expected-sampler-sha256', $o{sampler_sha256},
    '--expected-admitted-compiler-sha256', $o{admitted_compiler_sha256},
    '--expected-script-sha256', 'none', '--runner',
    parent_fd_path($held{'role:shared_runner'}[0]),
    '--runner-sha256', $o{runner_sha256}, '--candidate-builder',
    parent_fd_path($held{'role:candidate_builder'}[0]),
    '--candidate-builder-sha256', $o{candidate_builder_sha256},
    '--shell', parent_fd_path($held{'role:dash'}[0]),
    '--shell-sha256', $o{dash_sha256},
    '--candidate-provenance', parent_fd_path($held{candidate_provenance}[0]),
    '--candidate-provenance-sha256', $candidate_provenance_identity->{sha256},
    '--candidate-provenance-verify-receipt',
    parent_fd_path($held{candidate_verify}[0]),
    '--candidate-provenance-verify-receipt-sha256', $candidate_verify_identity->{sha256},
    '--output-dir', $analysis_output,
);
my $analyzer_status = run_bound_child($analyzer_exec_fh, 120_000, @analyzer_argv);
$analyzer_status == 0 or die "stage3 shared runner: analyzer failed ($analyzer_status)\n";
fail_if_interrupted('analyzer completion');

my $analyzer_receipt = "$analysis_output/receipt.env";
my ($analyzer_receipt_fh, $analyzer_receipt_identity, $analyzer_value,
    $analyzer_order, $analyzer_text) = parse_receipt($analyzer_receipt, 1_048_576);
$held{analyzer_receipt} = [$analyzer_receipt_fh, $analyzer_receipt_identity];
my @expected_analyzer_order = qw(receipt_schema run_id result
    raw_dev raw_ino raw_sha256 memory_dev memory_ino memory_sha256
    phase_dev phase_ino phase_sha256 provenance_dev provenance_ino provenance_sha256
    descriptor_dev descriptor_ino descriptor_sha256 launch_plan_dev launch_plan_ino
    launch_plan_sha256 identity_manifest_dev identity_manifest_ino
    identity_manifest_sha256 provenance_verify_receipt_dev
    provenance_verify_receipt_ino provenance_verify_receipt_sha256
    candidate_provenance_path candidate_provenance_dev candidate_provenance_ino
    candidate_provenance_sha256 candidate_provenance_verify_receipt_path
    candidate_provenance_verify_receipt_dev candidate_provenance_verify_receipt_ino
    candidate_provenance_verify_receipt_sha256 admitted_compiler_path
    admitted_compiler_dev admitted_compiler_ino admitted_compiler_sha256
    produced_candidate_path produced_candidate_dev produced_candidate_ino
    produced_candidate_sha256 sampler_dev sampler_ino sampler_sha256 analyzer_dev
    analyzer_ino analyzer_sha256 measured_command_dev measured_command_ino
    measured_command_sha256 measured_script_dev measured_script_ino
    measured_script_sha256 runner_dev runner_ino runner_sha256 candidate_builder_dev
    candidate_builder_ino candidate_builder_sha256 orchestration_shell_dev
    orchestration_shell_ino orchestration_shell_sha256 environment_sha256
    argv_semantic_sha256 environment_semantic_sha256 boundary_sha256 delta_sha256
    summary_sha256 sample_interval_ms max_gap_ms max_summed_rss_kib compiler_wall_ms
    max_sample_batches max_process_records max_tracked_processes
    raw_evidence_max_bytes term_grace_ms kill_reap_deadline_ms closure_reserve_bytes
    closure_reserve_records physical_sources phase_mode observed_max_start_gap_ns
    observed_max_batch_duration_ns memory_bytes memory_records phase_bytes phase_records
    descriptor_records identity_records plan_records provenance_verify_records);
join("\0", @$analyzer_order) eq join("\0", @expected_analyzer_order)
    or die "stage3 shared runner: analyzer receipt key/order mismatch\n";
my %required_analyzer = (
    receipt_schema => 'simple-stage3-memory-evidence-v2', run_id => $o{run_id},
    result => 'complete', launch_plan_dev => "$plan_identity->{dev}",
    launch_plan_ino => "$plan_identity->{ino}",
    launch_plan_sha256 => $plan_identity->{sha256},
    identity_manifest_dev => "$identity_identity->{dev}",
    identity_manifest_ino => "$identity_identity->{ino}",
    identity_manifest_sha256 => $identity_identity->{sha256},
    raw_dev => "$raw_identity->{dev}", raw_ino => "$raw_identity->{ino}",
    raw_sha256 => $raw_identity->{sha256},
    memory_dev => "$memory_identity->{dev}", memory_ino => "$memory_identity->{ino}",
    memory_sha256 => $memory_identity->{sha256},
    phase_dev => "$phase_identity->{dev}", phase_ino => "$phase_identity->{ino}",
    phase_sha256 => $phase_identity->{sha256},
    provenance_dev => "$artifact_identity{parent_provenance}{dev}",
    provenance_ino => "$artifact_identity{parent_provenance}{ino}",
    provenance_sha256 => $artifact_identity{parent_provenance}{sha256},
    descriptor_dev => "$artifact_identity{descriptor}{dev}",
    descriptor_ino => "$artifact_identity{descriptor}{ino}",
    descriptor_sha256 => $artifact_identity{descriptor}{sha256},
    provenance_verify_receipt_dev => "$artifact_identity{parent_provenance_verify}{dev}",
    provenance_verify_receipt_ino => "$artifact_identity{parent_provenance_verify}{ino}",
    provenance_verify_receipt_sha256 => $artifact_identity{parent_provenance_verify}{sha256},
    candidate_provenance_path =>
        token_v2(parent_fd_path($held{candidate_provenance}[0])),
    candidate_provenance_dev => "$candidate_provenance_identity->{dev}",
    candidate_provenance_ino => "$candidate_provenance_identity->{ino}",
    candidate_provenance_sha256 => $candidate_provenance_identity->{sha256},
    candidate_provenance_verify_receipt_path =>
        token_v2(parent_fd_path($held{candidate_verify}[0])),
    candidate_provenance_verify_receipt_dev => "$candidate_verify_identity->{dev}",
    candidate_provenance_verify_receipt_ino => "$candidate_verify_identity->{ino}",
    candidate_provenance_verify_receipt_sha256 => $candidate_verify_identity->{sha256},
    admitted_compiler_path => token_v2($o{admitted_compiler}),
    admitted_compiler_dev => "$role_identity{admitted_compiler}{dev}",
    admitted_compiler_ino => "$role_identity{admitted_compiler}{ino}",
    admitted_compiler_sha256 => $role_identity{admitted_compiler}{sha256},
    produced_candidate_path => token_v2($o{candidate_output}),
    produced_candidate_dev => "$candidate_identity->{dev}",
    produced_candidate_ino => "$candidate_identity->{ino}",
    produced_candidate_sha256 => $candidate_identity->{sha256},
    sampler_dev => "$role_identity{sampler}{dev}",
    sampler_ino => "$role_identity{sampler}{ino}",
    sampler_sha256 => $role_identity{sampler}{sha256},
    analyzer_dev => "$role_identity{analyzer}{dev}",
    analyzer_ino => "$role_identity{analyzer}{ino}",
    analyzer_sha256 => $role_identity{analyzer}{sha256},
    measured_command_dev => "$role_identity{admitted_compiler}{dev}",
    measured_command_ino => "$role_identity{admitted_compiler}{ino}",
    measured_command_sha256 => $role_identity{admitted_compiler}{sha256},
    measured_script_dev => '0', measured_script_ino => '0',
    measured_script_sha256 => 'none',
    runner_dev => "$role_identity{shared_runner}{dev}",
    runner_ino => "$role_identity{shared_runner}{ino}",
    runner_sha256 => $role_identity{shared_runner}{sha256},
    candidate_builder_dev => "$role_identity{candidate_builder}{dev}",
    candidate_builder_ino => "$role_identity{candidate_builder}{ino}",
    candidate_builder_sha256 => $role_identity{candidate_builder}{sha256},
    orchestration_shell_dev => "$role_identity{dash}{dev}",
    orchestration_shell_ino => "$role_identity{dash}{ino}",
    orchestration_shell_sha256 => $role_identity{dash}{sha256},
    environment_sha256 => semantic_environment_hash(),
    argv_semantic_sha256 => semantic_argv_hash(),
    environment_semantic_sha256 => semantic_environment_hash(),
    sample_interval_ms => '5', max_gap_ms => '50',
    max_summed_rss_kib => '8388608', compiler_wall_ms => '3600000',
    max_sample_batches => '1000000', max_process_records => '16000000',
    max_tracked_processes => '4096', raw_evidence_max_bytes => '1073741824',
    term_grace_ms => '5000', kill_reap_deadline_ms => '10000',
    closure_reserve_bytes => '65536', closure_reserve_records => '256',
    phase_mode => 'streaming', plan_records => '60', identity_records => '17',
    provenance_verify_records => '10',
);
for my $key (sort keys %required_analyzer) {
    exists($analyzer_value->{$key}) && $analyzer_value->{$key} eq $required_analyzer{$key}
        or die "stage3 shared runner: analyzer receipt mismatch for $key\n";
}
for my $key (qw(boundary_sha256 delta_sha256 summary_sha256)) {
    valid_sha($analyzer_value->{$key})
        or die "stage3 shared runner: analyzer receipt invalid hash for $key\n";
}
for my $key (qw(physical_sources observed_max_start_gap_ns
        observed_max_batch_duration_ns memory_bytes memory_records phase_bytes
        phase_records descriptor_records identity_records plan_records
        provenance_verify_records)) {
    defined($analyzer_value->{$key}) && $analyzer_value->{$key} =~ /\A[0-9]+\z/
        or die "stage3 shared runner: analyzer receipt invalid count for $key\n";
}
$analyzer_value->{physical_sources} > 0 &&
    $analyzer_value->{memory_bytes} > 0 && $analyzer_value->{memory_records} > 0 &&
    $analyzer_value->{phase_bytes} > 0 && $analyzer_value->{phase_records} > 0 &&
    $analyzer_value->{descriptor_records} > 0 &&
    $analyzer_value->{observed_max_start_gap_ns} <= 50_000_000 &&
    $analyzer_value->{observed_max_batch_duration_ns} <= 50_000_000
    or die "stage3 shared runner: analyzer receipt evidence count/gap mismatch\n";

for my $name (sort keys %held) {
    stable_identity(@{$held{$name}})
        or die "stage3 shared runner: retained identity changed for $name\n";
}
fail_if_interrupted('retained identity validation');

$console_fh->sync or die "stage3 shared runner: fsync console log: $!\n";
close($console_fh) or die "stage3 shared runner: close console log: $!\n";
undef $console_fh;
my $console_identity = identity_of_path($console_log);
my $marker_receipt_identity = identity_of_path("$o{compatibility_marker}/compatibility.env");

my $component_text = join('',
    "schema=simple-stage3-shared-runner-receipt-v1\n",
    "status=component-pass\n", "authority=false\n",
    "transaction_admission=false\n", "unit_zero_authority=false\n",
    "run_id=$o{run_id}\n", "architecture=$o{architecture}\n",
    "unit_launch_plan_dev=$unit_plan_identity->{dev}\n",
    "unit_launch_plan_ino=$unit_plan_identity->{ino}\n",
    "unit_launch_plan_sha256=$unit_plan_identity->{sha256}\n",
    "stage3_launch_plan_dev=$plan_identity->{dev}\n",
    "stage3_launch_plan_ino=$plan_identity->{ino}\n",
    "stage3_launch_plan_sha256=$plan_identity->{sha256}\n",
    "helper_capsule_inventory_dev=$helper_capsule_inventory_identity->{dev}\n",
    "helper_capsule_inventory_ino=$helper_capsule_inventory_identity->{ino}\n",
    "helper_capsule_inventory_sha256=$helper_capsule_inventory_identity->{sha256}\n",
    "helper_capsule_sha256=$helper_capsule_identity->{sha256}\n",
    "helper_capsule_entry_parity_sha256=$capsule_parity_sha256\n",
    "compatibility_marker_dev=$marker_stat[0]\n",
    "compatibility_marker_ino=$marker_stat[1]\n",
    "compatibility_marker_receipt_sha256=$marker_receipt_identity->{sha256}\n",
    "raw_dev=$raw_identity->{dev}\n", "raw_ino=$raw_identity->{ino}\n",
    "raw_sha256=$raw_identity->{sha256}\n",
    "memory_dev=$memory_identity->{dev}\n", "memory_ino=$memory_identity->{ino}\n",
    "memory_sha256=$memory_identity->{sha256}\n",
    "phase_dev=$phase_identity->{dev}\n", "phase_ino=$phase_identity->{ino}\n",
    "phase_sha256=$phase_identity->{sha256}\n",
    "candidate_output_dev=$candidate_identity->{dev}\n",
    "candidate_output_ino=$candidate_identity->{ino}\n",
    "candidate_output_sha256=$candidate_identity->{sha256}\n",
    "candidate_provenance_sha256=$candidate_provenance_identity->{sha256}\n",
    "candidate_provenance_verify_receipt_sha256=$candidate_verify_identity->{sha256}\n",
    "analyzer_receipt_dev=$analyzer_receipt_identity->{dev}\n",
    "analyzer_receipt_ino=$analyzer_receipt_identity->{ino}\n",
    "analyzer_receipt_sha256=$analyzer_receipt_identity->{sha256}\n",
    "console_log_dev=$console_identity->{dev}\n", "console_log_ino=$console_identity->{ino}\n",
    "console_log_sha256=$console_identity->{sha256}\n",
    "sampler_sha256=$o{sampler_sha256}\n", "analyzer_sha256=$o{analyzer_sha256}\n",
    "runner_sha256=$o{runner_sha256}\n", "candidate_builder_sha256=$o{candidate_builder_sha256}\n",
    "dash_sha256=$o{dash_sha256}\n", "provenance_verifier_sha256=$o{provenance_verifier_sha256}\n",
    "cleanup=measured-subtree-zero-analyzer-complete\n");
# The PASS bytes live only in an anonymous, fsynced inode until the final
# no-replace link.  Every named precommit record is explicitly non-PASS, so a
# crash, fsync failure, or cleanup failure before that link cannot expose a
# canonical success result.
my $pass_fh = anonymous_pass_inode($unit_evidence_dir_fh, $component_text, 0600);
my @pass_stat = stat($pass_fh);
@pass_stat && -f _ or die "stage3 shared runner: anonymous PASS identity\n";
my $pass_identity = {
    dev => $pass_stat[0], ino => $pass_stat[1], sha256 => hash_fh($pass_fh),
};
my $prepared_leaf = ".runner-receipt.prepared.$o{run_id}";
my $prepared_text = join('',
    "schema=simple-stage3-shared-runner-prepared-v1\n", "status=prepared\n",
    "run_id=$o{run_id}\n", "canonical_status=not-published\n",
    "pass_dev=$pass_identity->{dev}\n", "pass_ino=$pass_identity->{ino}\n",
    "pass_sha256=$pass_identity->{sha256}\n");
my $prepared_identity = publish_exclusive_at(
    $unit_evidence_dir_fh, $prepared_leaf, $prepared_text, 0600);
my $commit_leaf = ".runner-receipt.commit.$o{run_id}";
my $commit_text = join('',
    "schema=simple-stage3-shared-runner-commit-v1\n", "status=prepared\n",
    "run_id=$o{run_id}\n", "canonical_status=not-published\n",
    "prepared_dev=$prepared_identity->{dev}\n",
    "prepared_ino=$prepared_identity->{ino}\n",
    "prepared_sha256=$prepared_identity->{sha256}\n",
    "pass_dev=$pass_identity->{dev}\n", "pass_ino=$pass_identity->{ino}\n",
    "pass_sha256=$pass_identity->{sha256}\n");
publish_exclusive_at($unit_evidence_dir_fh, $commit_leaf, $commit_text, 0600);

# Canonical PASS publication is intentionally the last operation.  linkat is
# no-replace; collision cannot alter the incumbent.  The durable commit record
# lets recovery distinguish a post-link crash from an uncommitted prepared
# inode without any fallible cleanup or fsync after PASS becomes visible.
begin_canonical_pass_commit();
link_anonymous_final($pass_fh, $unit_evidence_dir_fh, 'runner-receipt.env');
POSIX::_exit(0);
