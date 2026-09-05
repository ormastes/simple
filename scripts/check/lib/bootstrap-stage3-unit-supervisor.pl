#!/usr/bin/env perl
use strict;
use warnings;
use Digest::SHA qw(sha256_hex);
use Errno qw(EINTR EEXIST);
use Fcntl qw(:DEFAULT :flock :mode F_GETFD F_SETFD FD_CLOEXEC
    O_NOFOLLOW O_DIRECTORY);
use File::Basename qw(dirname);
use Getopt::Long qw(GetOptions);
use IO::Handle;
use IO::Select;
use POSIX qw(WNOHANG dup2);
use Time::HiRes qw(clock_gettime sleep CLOCK_MONOTONIC);

# Perl's Fcntl on supported Linux hosts does not consistently export the
# kernel O_CLOEXEC macro. Linux asm-generic fixes it at octal 02000000 for all
# three admitted architectures; the immediate F_GETFD assertion below makes a
# host mismatch fail closed before the lock can authorize work.
my $O_CLOEXEC = 02000000;

my %o = (
    systemd_run => '/usr/bin/systemd-run',
    systemctl => '/usr/bin/systemctl',
    cgroup_root => '/sys/fs/cgroup',
    service_timeout_ms => 3_900_000,
    stop_timeout_ms => 30_000,
    helper_timeout_ms => 5_000,
);
my (@env, @role, @arg);
GetOptions(
    'phase=s' => \$o{phase}, 'root=s' => \$o{root},
    'evidence-dir=s' => \$o{evidence}, 'run-id=s' => \$o{run_id},
    'architecture=s' => \$o{architecture}, 'memory-max=i' => \$o{memory_max},
    'heavy-lock=s' => \$o{heavy_lock}, 'owner-journal=s' => \$o{owner_journal},
    'quarantine=s' => \$o{quarantine}, 'systemd-run=s' => \$o{systemd_run},
    'systemctl=s' => \$o{systemctl}, 'cgroup-root=s' => \$o{cgroup_root},
    'env=s@' => \@env, 'role=s@' => \@role, 'arg=s@' => \@arg,
    'service-timeout-ms=i' => \$o{service_timeout_ms},
    'stop-timeout-ms=i' => \$o{stop_timeout_ms},
    'helper-timeout-ms=i' => \$o{helper_timeout_ms},
    'allow-test-hooks!' => \$o{allow_test_hooks},
) or die "stage3 unit supervisor: invalid options\n";

my $parent_pid = $$;
my $lock_fh;
my $root_fh;
my $systemd_pid;
my $unit_spawned = 0;
my $unit = '';
my $cleanup_armed = 0;
my $journal_owned = 0;
my $cgroup_journal_owned = 0;
my $interrupted = '';
my $cgroup_fh;
my $helper_waitpid_eintr_injected = 0;
my $systemctl_read_error_injected = 0;

sub now_ms { int(clock_gettime(CLOCK_MONOTONIC) * 1000) }
sub test_barrier {
    my ($point) = @_;
    return unless $o{allow_test_hooks};
    return unless ($ENV{STAGE3_SUPERVISOR_TEST_BARRIER_POINT} // '') eq $point;
    my $reached = $ENV{STAGE3_SUPERVISOR_TEST_BARRIER_REACHED} // '';
    my $release = $ENV{STAGE3_SUPERVISOR_TEST_BARRIER_RELEASE} // '';
    $reached =~ m{\A/} && $release =~ m{\A/} && -p $reached && -p $release
        or die "invalid test barrier FIFOs\n";
    sysopen(my $out, $reached, O_WRONLY | O_NOFOLLOW | $O_CLOEXEC)
        or die "open reached barrier: $!\n";
    print {$out} "$point\n" or die "write reached barrier: $!\n";
    close($out) or die "close reached barrier: $!\n";
    sysopen(my $in, $release, O_RDONLY | O_NOFOLLOW | $O_CLOEXEC)
        or die "open release barrier: $!\n";
    my $ack = <$in>;
    close($in) or die "close release barrier: $!\n";
    defined($ack) && $ack eq "continue\n"
        or die "invalid test barrier release\n";
}
sub set_cloexec {
    my ($fh, $enabled) = @_;
    my $flags = fcntl($fh, F_GETFD, 0);
    defined($flags) or die "read descriptor flags: $!\n";
    $flags = $enabled ? ($flags | FD_CLOEXEC) : ($flags & ~FD_CLOEXEC);
    fcntl($fh, F_SETFD, $flags) or die "write descriptor flags: $!\n";
}
sub absolute_dir {
    my ($path) = @_;
    $path =~ m{\A/} && -d $path && !-l $path
        or die "not an absolute physical directory: $path\n";
}
sub absolute_file {
    my ($path) = @_;
    $path =~ m{\A/} && -f $path && !-l $path
        or die "not an absolute physical file: $path\n";
}
sub open_regular {
    my ($path) = @_;
    absolute_file($path);
    sysopen(my $fh, $path, O_RDONLY | O_NOFOLLOW)
        or die "open $path: $!\n";
    set_cloexec($fh, 1);
    my @st = stat($fh);
    @st && -f _ or die "descriptor is not regular: $path\n";
    my @pst = lstat($path);
    @pst && $pst[0] == $st[0] && $pst[1] == $st[1]
        or die "identity changed while opening: $path\n";
    return $fh;
}
sub open_directory {
    my ($path) = @_;
    absolute_dir($path);
    sysopen(my $fh, $path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | $O_CLOEXEC)
        or die "open directory $path: $!\n";
    my $flags = fcntl($fh, F_GETFD, 0);
    defined($flags) && ($flags & FD_CLOEXEC)
        or die "directory was not opened atomically close-on-exec: $path\n";
    my @held = stat($fh); my @path = lstat($path);
    @held && @path && -d _ &&
        $held[0] == $path[0] && $held[1] == $path[1]
        or die "directory identity changed while opening: $path\n";
    return $fh;
}
sub open_regular_beneath {
    my ($root, $relative) = @_;
    $relative =~ m{\A[A-Za-z0-9._/-]+\z} && $relative !~ m{\A/|//} &&
        $relative !~ m{(?:\A|/)\.\.?(?:/|\z)}
        or die "unsafe relative authority path: $relative\n";
    my @parts = split m{/}, $relative;
    my $leaf = pop @parts;
    my $parent = $root;
    my @held_directories;
    for my $part (@parts) {
        my $path = "/proc/self/fd/" . fileno($parent) . "/$part";
        sysopen(my $next, $path,
            O_RDONLY | O_DIRECTORY | O_NOFOLLOW | $O_CLOEXEC)
            or die "open authority directory $relative: $!\n";
        my $flags = fcntl($next, F_GETFD, 0);
        my @st = stat($next);
        defined($flags) && ($flags & FD_CLOEXEC) && @st && -d _
            or die "invalid authority directory $relative\n";
        push @held_directories, $next;
        $parent = $next;
    }
    my $path = "/proc/self/fd/" . fileno($parent) . "/$leaf";
    sysopen(my $fh, $path,
        O_RDONLY | O_NONBLOCK | O_NOFOLLOW | $O_CLOEXEC)
        or die "open authority file $relative: $!\n";
    my $flags = fcntl($fh, F_GETFD, 0);
    my @st = stat($fh);
    defined($flags) && ($flags & FD_CLOEXEC) && @st && -f _
        or die "invalid authority file $relative\n";
    return $fh;
}
sub read_all {
    my ($fh) = @_;
    seek($fh, 0, 0) or die "seek descriptor: $!\n";
    local $/;
    my $value = <$fh>;
    defined($value) or die "read descriptor: $!\n";
    return $value;
}
sub hash_fh {
    my ($fh) = @_;
    seek($fh, 0, 0) or die "seek hash descriptor: $!\n";
    my $sha = Digest::SHA->new(256);
    $sha->addfile($fh);
    seek($fh, 0, 0) or die "rewind hash descriptor: $!\n";
    return $sha->hexdigest;
}
sub open_child_directory_fh {
    my ($parent, $leaf, $name) = @_;
    $leaf =~ /\A[A-Za-z0-9._-]+\z/
        or die "unsafe $name leaf\n";
    my $path = '/proc/self/fd/' . fileno($parent) . "/$leaf";
    sysopen(my $fh, $path,
        O_RDONLY | O_DIRECTORY | O_NOFOLLOW | $O_CLOEXEC)
        or die "open $name: $!\n";
    my @st = stat($fh);
    @st && -d _ or die "invalid $name directory\n";
    return $fh;
}
sub hash_stage2_directory {
    my ($root, $name) = @_;
    my $path = '/proc/self/fd/' . fileno($root);
    opendir(my $dir, $path) or die "enumerate $name: $!\n";
    my @entries = sort grep { $_ ne '.' && $_ ne '..' } readdir($dir);
    closedir($dir) or die "close $name enumeration: $!\n";
    my $digest = Digest::SHA->new(256);
    $digest->add("simple-stage2-directory-v1\0");
    for my $leaf (@entries) {
        $leaf !~ m{/|\0} or die "unsafe $name entry\n";
        my $entry_path = "$path/$leaf";
        my @st = lstat($entry_path);
        @st or die "stat $name/$leaf: $!\n";
        my $mode = sprintf('%04o', $st[2] & 07777);
        if (-d _ && !-l _) {
            my $child = open_child_directory_fh($root, $leaf, "$name/$leaf");
            my @held = stat($child);
            @held && $held[0] == $st[0] && $held[1] == $st[1]
                or die "changed directory $name/$leaf\n";
            my $hash = hash_stage2_directory($child, "$name/$leaf");
            $digest->add(join("\0", 'D', $leaf, $mode, $hash), "\0");
        } elsif (-f _ && !-l _) {
            sysopen(my $file, $entry_path,
                O_RDONLY | O_NOFOLLOW | $O_CLOEXEC)
                or die "open $name/$leaf: $!\n";
            my @held = stat($file);
            @held && $held[0] == $st[0] && $held[1] == $st[1]
                or die "changed file $name/$leaf\n";
            my $hash = hash_fh($file);
            close($file) or die "close $name/$leaf: $!\n";
            $digest->add(join("\0", 'F', $leaf, $mode, $st[7], $hash), "\0");
        } elsif (-l _) {
            my $target = readlink($entry_path);
            defined($target) or die "read $name/$leaf link: $!\n";
            $digest->add(join("\0", 'L', $leaf, $mode, $target), "\0");
        } else {
            die "unsupported entry $name/$leaf\n";
        }
    }
    return $digest->hexdigest;
}
sub hash_file {
    my ($path) = @_;
    my $fh = open_regular($path);
    my $hash = hash_fh($fh);
    close($fh) or die "close hashed file $path: $!\n";
    return $hash;
}
sub vector_hash {
    my (@values) = @_;
    my $bytes = '';
    for my $value (@values) {
        $bytes .= pack('Q>', length($value)) . $value;
    }
    return sha256_hex($bytes);
}
sub fsync_parent {
    my ($path) = @_;
    my $parent = dirname($path);
    absolute_dir($parent);
    sysopen(my $dfh, $parent, O_RDONLY | O_DIRECTORY | O_NOFOLLOW)
        or die "open parent directory $parent: $!\n";
    set_cloexec($dfh, 1);
    $dfh->sync or die "fsync parent directory $parent: $!\n";
    close($dfh) or die "close parent directory $parent: $!\n";
}
sub publish_exclusive {
    my ($path, $text, $mode, $purpose) = @_;
    my $parent = dirname($path);
    absolute_dir($parent);
    my $tmp = "$path.tmp.$parent_pid." . int(rand(1_000_000_000));
    sysopen(my $fh, $tmp, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW, $mode // 0600)
        or die "create publication temporary $tmp: $!\n";
    set_cloexec($fh, 1);
    my $offset = 0;
    while ($offset < length($text)) {
        my $written = syswrite($fh, $text, length($text) - $offset, $offset);
        if (!defined($written)) { next if $! == EINTR; die "write $tmp: $!\n"; }
        $written > 0 or die "zero-length write to $tmp\n";
        $offset += $written;
    }
    $fh->sync or die "fsync $tmp: $!\n";
    close($fh) or die "close $tmp: $!\n";
    if (!link($tmp, $path)) {
        my $error = "$!";
        unlink($tmp) or die "publication collision and rollback failed for $tmp: $error; $!\n";
        fsync_parent($path);
        die "publication collision for $path: $error\n";
    }
    if ($o{allow_test_hooks} && ($purpose // '') eq 'terminal-commit' &&
            ($ENV{STAGE3_SUPERVISOR_TEST_FAIL_POINT} // '') eq
                'terminal-commit-parent-fsync') {
        die "injected terminal commit parent fsync failure\n";
    }
    fsync_parent($path);
    unlink($tmp) or die "remove publication temporary $tmp: $!\n";
    fsync_parent($path);
}
sub unlink_durable {
    my ($path) = @_;
    unlink($path) or die "unlink $path: $!\n";
    fsync_parent($path);
}
sub decode_status {
    my ($status) = @_;
    return 128 + ($status & 127) if $status & 127;
    return $status >> 8;
}
sub wait_bounded {
    my ($pid, $timeout_ms) = @_;
    my $deadline = now_ms() + $timeout_ms;
    while (now_ms() < $deadline) {
        my $waited = waitpid($pid, WNOHANG);
        return decode_status($?) if $waited == $pid;
        die "waitpid $pid failed: $!\n" if $waited < 0;
        last if length($interrupted);
        sleep(0.01);
    }
    return;
}
sub wait_helper_cleanup {
    my ($pid, $timeout_ms) = @_;
    my $deadline = now_ms() + $timeout_ms;
    while (now_ms() < $deadline) {
        my $waited = helper_waitpid($pid, 'cleanup');
        return decode_status($?) if $waited == $pid;
        if ($waited < 0) {
            next if $! == EINTR;
            die "waitpid helper $pid failed: $!\n";
        }
        sleep(0.005);
    }
    return;
}
sub helper_waitpid {
    my ($pid, $phase) = @_;
    if ($o{allow_test_hooks} &&
            $phase eq 'preterm' &&
            ($ENV{STAGE3_SUPERVISOR_TEST_WAITPID_PRETERM_EINTR_ALWAYS} // '') eq '1') {
        $! = EINTR;
        return -1;
    }
    if ($o{allow_test_hooks} &&
            ($ENV{STAGE3_SUPERVISOR_TEST_WAITPID_EINTR_ONCE} // '') eq '1' &&
            !$helper_waitpid_eintr_injected) {
        $helper_waitpid_eintr_injected = 1;
        $! = EINTR;
        return -1;
    }
    return waitpid($pid, WNOHANG);
}
sub terminate_and_reap_helper {
    my ($pid) = @_;
    # This is a single nonblocking observation, never a retry loop. EINTR means
    # "not observed reaped" and proceeds immediately to bounded termination.
    my $waited = helper_waitpid($pid, 'preterm');
    return decode_status($?) if $waited == $pid;
    die "waitpid helper $pid failed: $!\n" if $waited < 0 && $! != EINTR;
    kill('TERM', $pid);
    my $status = wait_helper_cleanup($pid, $o{helper_timeout_ms});
    return $status if defined($status);
    kill('KILL', $pid);
    $status = wait_helper_cleanup($pid, $o{helper_timeout_ms});
    defined($status) or die "systemctl helper $pid survived TERM/KILL deadline\n";
    return $status;
}
sub exec_open_descriptor {
    my ($fh, @argv) = @_;
    set_cloexec($fh, 0);
    my $path = '/proc/self/fd/' . fileno($fh);
    exec {$path} @argv;
    POSIX::_exit(127);
}
sub close_descriptors_except {
    my (@keep) = @_;
    my %keep = map { $_ => 1 } @keep;
    opendir(my $dir, '/proc/self/fd') or POSIX::_exit(126);
    my @close = grep { /^\d+$/ && $_ > 2 && !$keep{$_} } readdir($dir);
    closedir($dir) or POSIX::_exit(126);
    POSIX::close($_) for @close;
}
sub capture_systemctl {
    my (@args) = @_;
    pipe(my $read, my $write) or die "systemctl pipe: $!\n";
    set_cloexec($read, 1); set_cloexec($write, 1);
    my $pid = fork();
    defined($pid) or die "fork systemctl: $!\n";
    if (!$pid) {
        $cleanup_armed = 0;
        $SIG{TERM} = $SIG{INT} = $SIG{HUP} = 'DEFAULT';
        close($read);
        open(STDOUT, '>&', $write) or POSIX::_exit(126);
        open(STDERR, '>', '/dev/null') or POSIX::_exit(126);
        close($write);
        exec_open_descriptor($o{systemctl_fh}, $o{systemctl}, '--user', @args);
    }
    close($write);
    my $deadline = now_ms() + $o{helper_timeout_ms};
    my $select = IO::Select->new($read);
    my $output = '';
    my $read_error = '';
    my $read_ok = eval {
        while (now_ms() < $deadline) {
            if ($o{allow_test_hooks} &&
                    ($ENV{STAGE3_SUPERVISOR_TEST_READ_ERROR_ONCE} // '') eq '1' &&
                    !$systemctl_read_error_injected) {
                $systemctl_read_error_injected = 1;
                die "read systemctl output: injected failure\n";
            }
            my $remaining = ($deadline - now_ms()) / 1000;
            my @ready = $select->can_read($remaining > 0 ? $remaining : 0);
            last unless @ready;
            my $buffer = '';
            my $count = sysread($read, $buffer, 4096);
            if (defined($count)) {
                length($output) + $count <= 65_536
                    or die "systemctl output exceeded bound\n";
                $output .= $buffer;
                last if $count == 0;
            } elsif ($! != EINTR) {
                die "read systemctl output: $!\n";
            }
            sleep(0.005);
        }
        1;
    };
    $read_error = $@ unless $read_ok;
    if (!close($read) && !length($read_error)) {
        $read_error = "close systemctl output: $!\n";
    }
    if (length($read_error)) {
        my $cleanup_ok = eval { terminate_and_reap_helper($pid); 1 };
        my $cleanup_error = $@;
        die $cleanup_ok ? $read_error : "$read_error$cleanup_error";
    }
    my $status;
    my $wait_ok = eval {
        $status = wait_bounded($pid, $o{helper_timeout_ms});
        1;
    };
    my $wait_error = $@;
    if (!$wait_ok) {
        my $cleanup_ok = eval { terminate_and_reap_helper($pid); 1 };
        my $cleanup_error = $@;
        die $cleanup_ok ? $wait_error : "$wait_error$cleanup_error";
    }
    if (!defined($status)) {
        terminate_and_reap_helper($pid);
        die "systemctl helper timeout\n";
    }
    return if $status != 0;
    $output =~ s/[\r\n]+\z//;
    return $output;
}
sub systemctl_value {
    my ($name) = @_;
    return capture_systemctl('show', "$unit.service", "--property=$name", '--value');
}
sub stop_and_reap_unit {
    return 1 unless length($unit);
    capture_systemctl('stop', "$unit.service");
    my $deadline = now_ms() + $o{stop_timeout_ms};
    while (now_ms() < $deadline) {
        my $active = systemctl_value('ActiveState');
        last if defined($active) && $active eq 'inactive';
        sleep(0.02);
    }
    my $active = systemctl_value('ActiveState');
    if (!defined($active) || $active ne 'inactive') {
        capture_systemctl('kill', '--signal=KILL', '--kill-who=all', "$unit.service");
    }
    if (defined($systemd_pid)) {
        my $status = wait_bounded($systemd_pid, $o{stop_timeout_ms});
        if (!defined($status)) {
            kill('TERM', $systemd_pid); sleep(0.1); kill('KILL', $systemd_pid);
            waitpid($systemd_pid, 0);
        }
        undef $systemd_pid;
    }
    $active = systemctl_value('ActiveState');
    return defined($active) && $active eq 'inactive';
}
sub parse_counter_file {
    my ($text) = @_;
    my %values;
    for my $line (split /\n/, $text) {
        next if $line eq '';
        $line =~ /\A([a-z_]+) ([0-9]+)\z/
            or die "malformed cgroup counter row\n";
        !exists($values{$1}) or die "duplicate cgroup counter $1\n";
        $values{$1} = 0 + $2;
    }
    return %values;
}
sub prove_held_cgroup_empty {
    return 0 unless defined($cgroup_fh);
    my $base = '/proc/self/fd/' . fileno($cgroup_fh);
    sysopen(my $events, "$base/cgroup.events", O_RDONLY | O_NOFOLLOW) or return 0;
    set_cloexec($events, 1);
    my %counter = eval { parse_counter_file(read_all($events)) };
    return 0 if $@;
    return exists($counter{populated}) && $counter{populated} == 0;
}
sub quarantine_locked {
    my ($reason) = @_;
    defined($lock_fh) or die "quarantine requires the heavy lock\n";
    return if -e $o{quarantine} || -l $o{quarantine};
    my $receipt = join('',
        "schema=simple-stage3-global-quarantine-v1\n",
        "architecture=$o{architecture}\n", "run_id=$o{run_id}\n",
        "unit=" . (length($unit) ? $unit : 'unassigned') . "\n",
        "reason=$reason\n");
    publish_exclusive($o{quarantine}, $receipt, 0600);
}
sub read_receipt {
    my ($path) = @_;
    my $fh = open_regular($path);
    my %value;
    for my $line (split /\n/, read_all($fh)) {
        next if $line eq '';
        $line =~ /\A([a-z0-9_]+)=(.*)\z/s or die "malformed receipt $path\n";
        !exists($value{$1}) or die "duplicate key $1 in $path\n";
        $value{$1} = $2;
    }
    close($fh) or die "close receipt $path: $!\n";
    return %value;
}
sub receipt_has_exact_keys {
    my ($state, @keys) = @_;
    return join("\0", sort keys %$state) eq join("\0", sort @keys);
}
sub canonical_cgroup_path {
    my ($path, $expected_unit) = @_;
    return 0 unless defined($path) && $path =~ m{\A/} && $path !~ m{//};
    my @component = split m{/}, substr($path, 1), -1;
    return 0 unless @component;
    for my $component (@component) {
        return 0 if $component eq '' || $component eq '.' || $component eq '..';
        return 0 unless $component =~ /\A[A-Za-z0-9_.:-]+\z/;
    }
    return $component[-1] eq $expected_unit ||
        $component[-1] eq "$expected_unit.service";
}
sub recover_stale_journal {
    my ($expected_unit) = @_;
    return unless -e $o{owner_journal} || -l $o{owner_journal};
    my %state = eval { read_receipt($o{owner_journal}) };
    if ($@ || !receipt_has_exact_keys(\%state, qw(schema architecture run_id
            phase unit supervisor_pid)) ||
            ($state{schema} // '') ne 'simple-stage3-unit-owner-v1' ||
            ($state{architecture} // '') ne $o{architecture} ||
            ($state{phase} // '') ne $o{phase} ||
            ($state{run_id} // '') !~ /\A[A-Za-z0-9_-]{8,64}\z/ ||
            ($state{unit} // '') ne $expected_unit ||
            ($state{supervisor_pid} // '') !~ /\A[1-9][0-9]*\z/) {
        quarantine_locked('malformed-stale-owner-journal');
        die "malformed stale owner journal\n";
    }
    if (-e "/proc/$state{supervisor_pid}") {
        quarantine_locked('stale-owner-supervisor-still-live');
        die "stale owner supervisor is still live\n";
    }
    my $cgpath = "$o{owner_journal}.cgroup";
    my %cg = eval { read_receipt($cgpath) };
    if ($@ || !receipt_has_exact_keys(\%cg, qw(schema architecture run_id
            phase unit cgroup cgroup_dev cgroup_ino)) ||
            ($cg{schema} // '') ne 'simple-stage3-active-cgroup-v1' ||
            ($cg{architecture} // '') ne $o{architecture} ||
            ($cg{run_id} // '') ne $state{run_id} ||
            ($cg{phase} // '') ne $o{phase} ||
            ($cg{unit} // '') ne $expected_unit ||
            !canonical_cgroup_path($cg{cgroup}, $expected_unit) ||
            ($cg{cgroup_dev} // '') !~ /\A[0-9]+\z/ ||
            ($cg{cgroup_ino} // '') !~ /\A[1-9][0-9]*\z/) {
        quarantine_locked('malformed-stale-cgroup-journal');
        die "malformed stale cgroup journal\n";
    }
    $unit = $expected_unit;
    my $observed_control_group = systemctl_value('ControlGroup');
    if (!defined($observed_control_group) ||
            $observed_control_group ne $cg{cgroup}) {
        quarantine_locked('stale-control-group-mismatch');
        die "stale ControlGroup mismatch\n";
    }
    my $path = "$o{cgroup_root}$cg{cgroup}";
    sysopen(my $dfh, $path,
        O_RDONLY | O_DIRECTORY | O_NOFOLLOW | $O_CLOEXEC)
        or do {
            quarantine_locked('stale-cgroup-open-failed');
            die "open stale cgroup: $!\n";
        };
    my @st = stat($dfh);
    if (!@st || "$st[0]" ne $cg{cgroup_dev} || "$st[1]" ne $cg{cgroup_ino}) {
        close($dfh);
        quarantine_locked('stale-cgroup-identity-mismatch');
        die "stale cgroup identity mismatch\n";
    }
    $cgroup_fh = $dfh;
    my $stopped = eval { stop_and_reap_unit() };
    my $stop_error = $@;
    my $empty = !$stop_error && $stopped && prove_held_cgroup_empty();
    if (!$stopped || !$empty || length($stop_error)) {
        quarantine_locked('stale-owner-zero-proof-failed');
        die "stale unit could not be proved inactive and empty\n";
    }
    close($cgroup_fh) or do {
        quarantine_locked('stale-cgroup-close-failed');
        die "close stale cgroup: $!\n";
    };
    undef $cgroup_fh;
    unlink_durable("$o{owner_journal}.cgroup");
    unlink_durable($o{owner_journal});
    $unit = '';
}
sub copy_role_snapshot {
    my ($name, $src, $destination) = @_;
    sysopen(my $dst, $destination, O_RDWR | O_CREAT | O_EXCL | O_NOFOLLOW, 0500)
        or die "create role snapshot $destination: $!\n";
    set_cloexec($dst, 1);
    my $buffer;
    while (1) {
        my $count = sysread($src, $buffer, 65_536);
        if (!defined($count)) { next if $! == EINTR; die "read role $name: $!\n"; }
        last if $count == 0;
        my $offset = 0;
        while ($offset < $count) {
            my $written = syswrite($dst, $buffer, $count - $offset, $offset);
            if (!defined($written)) { next if $! == EINTR; die "write role $name: $!\n"; }
            $written > 0 or die "zero write for role $name\n";
            $offset += $written;
        }
    }
    $dst->sync or die "fsync role $name: $!\n";
    my $source_hash = hash_fh($src);
    my $copy_hash = hash_fh($dst);
    $source_hash eq $copy_hash or die "role snapshot hash mismatch for $name\n";
    my @writable_identity = stat($dst);
    @writable_identity && -f _ or die "role snapshot type mismatch for $name\n";
    close($dst) or die "close writable role snapshot $name: $!\n";
    sysopen(my $held, $destination,
        O_RDONLY | O_NOFOLLOW | $O_CLOEXEC)
        or die "reopen read-only role snapshot $name: $!\n";
    set_cloexec($held, 1);
    my @held_identity = stat($held);
    my @named_identity = lstat($destination);
    @held_identity && @named_identity && -f _ && !-l _ &&
        $held_identity[0] == $writable_identity[0] &&
        $held_identity[1] == $writable_identity[1] &&
        $held_identity[0] == $named_identity[0] &&
        $held_identity[1] == $named_identity[1] &&
        hash_fh($held) eq $copy_hash
        or die "read-only role snapshot identity mismatch for $name\n";
    close($src) or die "close role source $name: $!\n";
    return ($copy_hash, $held);
}
sub validate_env {
    my %seen;
    my %denied = map { $_ => 1 } qw(LD_PRELOAD LD_LIBRARY_PATH LD_AUDIT
        PERL5OPT PERL5LIB PYTHONPATH PYTHONHOME BASH_ENV ENV SHELLOPTS GCONV_PATH
        SIMPLE_STAGE3_OUTER_LOCK_HELD SIMPLE_STAGE3_HEAVY_LOCK_CAPABILITY_FD
        SIMPLE_BOOTSTRAP_STAGE2_RUNNER_PRIVATE
        SIMPLE_BOOTSTRAP_OUTER_LOCK_PROOF);
    for my $entry (@env) {
        $entry =~ /\A([A-Z][A-Z0-9_]*)=(.*)\z/s or die "invalid service environment\n";
        my ($key, $value) = ($1, $2);
        !$seen{$key}++ or die "duplicate service environment key $key\n";
        !$denied{$key} or die "loader or interpreter injection key forbidden: $key\n";
        if ($key eq 'HOME' || $key eq 'TMPDIR') { absolute_dir($value); }
        if ($key eq 'PATH') {
            length($value) or die "PATH is empty\n";
            for my $path (split /:/, $value, -1) { absolute_dir($path); }
        }
    }
    for my $required (qw(HOME TMPDIR PATH LC_ALL LANG)) {
        $seen{$required} or die "missing service environment key $required\n";
    }
    grep($_ eq 'LC_ALL=C', @env) or die "LC_ALL must equal C\n";
    grep($_ eq 'LANG=C', @env) or die "LANG must equal C\n";
}

for my $key (qw(phase root evidence run_id architecture memory_max heavy_lock
        owner_journal quarantine systemd_run systemctl cgroup_root)) {
    defined($o{$key}) && length("$o{$key}") or die "missing --$key\n";
}
$0 =~ m{\A/} or die "supervisor must be invoked through an absolute path\n";
$o{phase} =~ /\A(?:stage2|stage3)\z/ or die "invalid phase\n";
$o{run_id} =~ /\A[A-Za-z0-9_-]{8,64}\z/ or die "invalid run id\n";
$o{architecture} =~ /\A(?:x86_64|aarch64|riscv64)-unknown-linux-gnu\z/
    or die "unsupported architecture\n";
my $expected_cap = $o{phase} eq 'stage2' ? 53_687_091_200 : 8_589_934_592;
$o{memory_max} == $expected_cap or die "frozen memory limit mismatch\n";
$o{service_timeout_ms} == 3_900_000 || $o{allow_test_hooks}
    or die "RuntimeMaxSec must remain 3900\n";
$o{stop_timeout_ms} == 30_000 || $o{allow_test_hooks}
    or die "stop timeout must remain 30000ms\n";
absolute_dir($o{root}); absolute_dir($o{cgroup_root});
$root_fh = open_directory($o{root});
my $root_exec = "/proc/$parent_pid/fd/" . fileno($root_fh);
for my $path ($o{systemd_run}, $o{systemctl}) { absolute_file($path); }
for my $path ($o{heavy_lock}, $o{owner_journal}, $o{quarantine}, $o{evidence}) {
    $path =~ m{\A/} or die "authority path must be absolute: $path\n";
    absolute_dir(dirname($path));
}
@role >= 3 or die "gate_interpreter, gate_helper, and payload roles are required\n";
@arg && $arg[0] eq '{role:payload}' or die "first payload arg must be {role:payload}\n";
validate_env();
my $lane_id = substr(sha256_hex("$o{root}\0$o{architecture}"), 0, 20);
my $expected_unit = "simple-stage3-$lane_id-$o{phase}";

sysopen($lock_fh, $o{heavy_lock},
    O_RDWR | O_CREAT | O_NOFOLLOW | $O_CLOEXEC, 0600)
    or die "open heavy lock: $!\n";
my $lock_fd_flags = fcntl($lock_fh, F_GETFD, 0);
defined($lock_fd_flags) && ($lock_fd_flags & FD_CLOEXEC)
    or die "heavy lock was not opened atomically close-on-exec\n";
flock($lock_fh, LOCK_EX | LOCK_NB) or die "heavy lock is busy\n";

(-e $o{quarantine} || -l $o{quarantine}) and die "architecture is globally quarantined\n";
$o{systemd_run_fh} = open_regular($o{systemd_run});
$o{systemctl_fh} = open_regular($o{systemctl});
recover_stale_journal($expected_unit);
(-e $o{evidence} || -l $o{evidence}) and die "evidence collision\n";
mkdir($o{evidence}, 0700) or die "create evidence directory: $!\n";
mkdir("$o{evidence}/roles", 0700) or die "create role snapshot directory: $!\n";

my @stage2_helper_inventory = (
    ['session', 'scripts/check/lib/portable-session-exec.pl'],
    ['planner_admission', 'scripts/check/lib/bootstrap-planner-admission-bound.shs'],
    ['cache_policy', 'scripts/bootstrap/bootstrap-cache-policy.shs'],
    ['jobs_policy', 'scripts/bootstrap/bootstrap-build-jobs-policy.shs'],
    ['provenance_facade', 'scripts/check/lib/bootstrap-stage3-provenance.shs'],
    ['provenance_authority', 'scripts/check/lib/bootstrap-stage3/authority.shs'],
    ['provenance_command', 'scripts/check/lib/bootstrap-stage3/command-snapshot.shs'],
    ['provenance_sanity', 'scripts/check/lib/bootstrap-stage3/sanity.shs'],
    ['provenance_manifest_write', 'scripts/check/lib/bootstrap-stage3/manifest-write.shs'],
    ['provenance_manifest_verify', 'scripts/check/lib/bootstrap-stage3/manifest-verify.shs'],
    ['provenance_self_test', 'scripts/check/lib/bootstrap-stage3/self-test.shs'],
    ['portable_lock_atomic', 'scripts/check/lib/portable-hardlink-lock.pl'],
    ['portable_process_lock', 'scripts/check/lib/portable-process-lock.shs'],
    ['authority_wiring', 'scripts/bootstrap/bootstrap-authority-wiring.shs'],
    ['stage4_provenance', 'scripts/check/lib/stage4-candidate-provenance.shs'],
    ['resume_stage4', 'scripts/bootstrap/resume-stage4-from-admitted.sh'],
    ['progress_watch', 'scripts/bootstrap/bootstrap-progress-watch.shs'],
    ['platform_detect', 'scripts/setup/platform-detect.shs'],
    ['candidate_frontend', 'scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs'],
    ['preserve_phase', 'scripts/bootstrap/preserve-phase-binary.shs'],
    ['stage2_receiver', 'scripts/check/check-bootstrap-stage2-struct-receiver.shs'],
    ['stage_log', 'scripts/check/check-stage-log-diagnosable.shs'],
    ['compiler_deadline', 'scripts/check/lib/bootstrap-stage2-compiler-deadline.shs'],
);
my (%helper_path, %helper_hash, %helper_fh, %helper_exec, %helper_dev, %helper_ino);
if ($o{phase} eq 'stage2') {
    mkdir("$o{evidence}/helpers", 0700)
        or die "create helper snapshot directory: $!\n";
    for my $entry (@stage2_helper_inventory) {
        my ($name, $relative) = @$entry;
        my $destination = "$o{evidence}/helpers/$name";
        my $source_fh = open_regular_beneath($root_fh, $relative);
        ($helper_hash{$name}, $helper_fh{$name}) =
            copy_role_snapshot($name, $source_fh, $destination);
        $helper_path{$name} = $destination;
        my @st = stat($helper_fh{$name});
        $helper_exec{$name} = "/proc/$parent_pid/fd/" . fileno($helper_fh{$name});
        ($helper_dev{$name}, $helper_ino{$name}) = @st[0, 1];
    }
    fsync_parent("$o{evidence}/helpers/session");
}

my %role_path;
my %role_hash;
my %role_fh;
my %role_exec;
for my $spec (@role) {
    $spec =~ /\A([a-z][a-z0-9_]*)=(\/.*)\z/s or die "invalid role binding\n";
    my ($name, $source) = ($1, $2);
    !exists($role_path{$name}) or die "duplicate role $name\n";
    my $destination = "$o{evidence}/roles/$name";
    my $source_fh = open_regular($source);
    ($role_hash{$name}, $role_fh{$name}) =
        copy_role_snapshot($name, $source_fh, $destination);
    $role_path{$name} = $destination;
    $role_exec{$name} = "/proc/$parent_pid/fd/" . fileno($role_fh{$name});
}
for my $required (qw(env gate_interpreter gate_helper payload)) {
    exists($role_path{$required}) or die "missing role $required\n";
}
fsync_parent("$o{evidence}/roles/payload");
my @payload;
for my $token (@arg) {
    if ($token =~ /\A\{role:([a-z][a-z0-9_]*)\}\z/) {
        exists($role_exec{$1}) or die "argv references unknown role $1\n";
        push @payload, $role_exec{$1};
    } else {
        push @payload, $token;
    }
}
if ($o{phase} eq 'stage2') {
    push @payload, map { "--helper=$_->[0]=$helper_exec{$_->[0]}" }
        @stage2_helper_inventory;
}
my ($stage2_transaction_root, $stage2_bootstrap_role);
if ($o{phase} eq 'stage2') {
    for my $token (@payload) {
        if ($token =~ /\A--transaction-root=(.*)\z/s) {
            !defined($stage2_transaction_root)
                or die "duplicate Stage 2 transaction root\n";
            $stage2_transaction_root = $1;
        } elsif ($token =~ /\A--bootstrap=(.*)\z/s) {
            !defined($stage2_bootstrap_role)
                or die "duplicate Stage 2 bootstrap role\n";
            $stage2_bootstrap_role = $1;
        } elsif ($token =~ /\A--(?:output|evidence-dir|private-home|private-tmp|private-cache)=/) {
            die "legacy Stage 2 sibling authority is forbidden\n";
        }
    }
    defined($stage2_transaction_root) &&
        $stage2_transaction_root =~ m{\A/} &&
        $stage2_transaction_root ne '/' &&
        $stage2_transaction_root !~ m{//|/\.(?:/|\z)|/\.\.(?:/|\z)|/\z}
        or die "missing or non-canonical Stage 2 transaction root\n";
    !(-e $stage2_transaction_root || -l $stage2_transaction_root)
        or die "Stage 2 transaction root collision\n";
    absolute_dir(dirname($stage2_transaction_root));
    defined($stage2_bootstrap_role)
        or die "missing Stage 2 bootstrap role\n";
}
my ($stage2_bootstrap_dev, $stage2_bootstrap_ino,
    $stage2_bootstrap_hash);
if ($o{phase} eq 'stage2') {
    my ($role_name) = grep {
        $role_exec{$_} eq $stage2_bootstrap_role
    } keys %role_exec;
    defined($role_name)
        or die "Stage 2 bootstrap is not a retained role descriptor\n";
    my @identity = stat($role_fh{$role_name});
    @identity or die "stat Stage 2 bootstrap role: $!\n";
    ($stage2_bootstrap_dev, $stage2_bootstrap_ino) = @identity[0, 1];
    $stage2_bootstrap_hash = $role_hash{$role_name};
}
my @gate_args = ("--phase=$o{phase}");
push @gate_args, "--heavy-lock=$o{heavy_lock}" if $o{phase} eq 'stage2';

$unit = $expected_unit;
my $owner_text = join('',
    "schema=simple-stage3-unit-owner-v1\n", "architecture=$o{architecture}\n",
    "run_id=$o{run_id}\n", "phase=$o{phase}\n", "unit=$unit\n",
    "supervisor_pid=$parent_pid\n");
publish_exclusive($o{owner_journal}, $owner_text, 0600);
$journal_owned = 1;
$cleanup_armed = 1;
$SIG{TERM} = sub { $interrupted ||= 'TERM'; };
$SIG{INT} = sub { $interrupted ||= 'INT'; };
$SIG{HUP} = sub { $interrupted ||= 'HUP'; };
test_barrier('owner-ready');
length($interrupted) and die "supervisor interrupted by $interrupted\n";

END {
    my $saved = $?;
    if ($$ == $parent_pid && $cleanup_armed) {
        my $ok = eval {
            if ($unit_spawned) {
                my $stopped = stop_and_reap_unit();
                my $empty = prove_held_cgroup_empty();
                if (!$stopped || !$empty) {
                    quarantine_locked('supervisor-failure-zero-proof-failed');
                    die "cleanup could not prove zero\n";
                }
            }
            if ($cgroup_journal_owned && -e "$o{owner_journal}.cgroup") {
                unlink_durable("$o{owner_journal}.cgroup");
                $cgroup_journal_owned = 0;
            }
            if ($journal_owned && -e $o{owner_journal}) {
                unlink_durable($o{owner_journal});
                $journal_owned = 0;
            }
            1;
        };
        if (!$ok) { warn "stage3 supervisor cleanup failed: $@"; }
    }
    $? = $saved;
}

pipe(my $gate_r, my $gate_w) or die "create pre-exec gate: $!\n";
set_cloexec($gate_r, 1); set_cloexec($gate_w, 1);
my @command = (
    $o{systemd_run}, '--user', '--wait', '--service-type=exec', '--pipe',
    '--quiet',
    "--unit=$unit", '-p', 'ExitType=cgroup', '-p', 'OOMPolicy=kill',
    '-p', 'KillMode=control-group', '-p', 'SendSIGKILL=yes',
    '-p', "MemoryMax=$o{memory_max}", '-p', 'MemorySwapMax=0',
    '-p', 'RuntimeMaxSec=3900', '-p', "WorkingDirectory=$root_exec", '--',
    $role_exec{env}, '-i', @env, $role_exec{gate_interpreter},
    $role_exec{gate_helper}, @gate_args, '--', @payload,
);

$systemd_pid = fork();
defined($systemd_pid) or die "fork systemd-run: $!\n";
if (!$systemd_pid) {
    $cleanup_armed = 0;
    $SIG{TERM} = $SIG{INT} = $SIG{HUP} = 'DEFAULT';
    close($gate_w);
    open(STDIN, '<&', $gate_r) or POSIX::_exit(126);
    close($gate_r);
    if ($o{phase} eq 'stage2') {
        # systemd-run --pipe transfers this exact stdout OFD to the service.
        # The gate moves it to descriptor 9 before any payload output, so the
        # supervisor's one flock capability crosses the unit boundary by dup,
        # never by reopening or reacquiring the lock.
        open(STDOUT, '+<&', $lock_fh) or POSIX::_exit(126);
        my $flags = fcntl(STDOUT, F_GETFD, 0);
        defined($flags) && !($flags & FD_CLOEXEC) or POSIX::_exit(126);
    }
    my $exec_fd = 3;
    defined(dup2(fileno($o{systemd_run_fh}), $exec_fd)) or POSIX::_exit(126);
    close_descriptors_except($exec_fd);
    my $exec_fh = IO::Handle->new_from_fd($exec_fd, 'r');
    defined($exec_fh) or POSIX::_exit(126);
    exec_open_descriptor($exec_fh, @command);
}
$unit_spawned = 1;
close($gate_r);

my $control_group;
my $ready_deadline = now_ms() + ($o{allow_test_hooks} ? 3_000 : 30_000);
while (now_ms() < $ready_deadline && !length($interrupted)) {
    $control_group = systemctl_value('ControlGroup');
    last if defined($control_group) && $control_group =~ m{\A/[A-Za-z0-9_.:/-]+\z};
    sleep(0.02);
}
defined($control_group) && $control_group =~ m{\A/[A-Za-z0-9_.:/-]+\z}
    or die "unit ControlGroup is missing or malformed\n";

my $cgroup_path = "$o{cgroup_root}$control_group";
sysopen($cgroup_fh, $cgroup_path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW)
    or die "open service cgroup: $!\n";
set_cloexec($cgroup_fh, 1);
my @cgroup_stat = stat($cgroup_fh);
my ($cgroup_dev, $cgroup_ino) = @cgroup_stat[0, 1];
my %cgfd;
my $cgbase = '/proc/self/fd/' . fileno($cgroup_fh);
for my $name (qw(cgroup.events memory.events memory.current memory.peak memory.max
        memory.swap.current memory.swap.max memory.oom.group)) {
    sysopen(my $fh, "$cgbase/$name", O_RDONLY | O_NOFOLLOW)
        or die "open held cgroup file $name: $!\n";
    set_cloexec($fh, 1);
    $cgfd{$name} = $fh;
}
my $max = read_all($cgfd{'memory.max'}); $max =~ s/\s+\z//;
$max eq "$o{memory_max}" or die "memory.max mismatch\n";
my $swap_max = read_all($cgfd{'memory.swap.max'}); $swap_max =~ s/\s+\z//;
$swap_max eq '0' or die "memory.swap.max mismatch\n";
my $swap_before = read_all($cgfd{'memory.swap.current'}); $swap_before =~ s/\s+\z//;
$swap_before eq '0' or die "nonzero swap baseline\n";
my $oom_group = read_all($cgfd{'memory.oom.group'}); $oom_group =~ s/\s+\z//;
$oom_group eq '1' or die "memory.oom.group mismatch\n";
my %events_before = parse_counter_file(read_all($cgfd{'memory.events'}));
for my $key (qw(max oom oom_kill oom_group_kill)) {
    exists($events_before{$key}) or die "memory.events lacks $key\n";
    $events_before{$key} == 0 or die "nonzero memory.events baseline for $key\n";
}

my $cgroup_text = join('',
    "schema=simple-stage3-active-cgroup-v1\n", "architecture=$o{architecture}\n",
    "run_id=$o{run_id}\n", "phase=$o{phase}\n", "unit=$unit\n",
    "cgroup=$control_group\n", "cgroup_dev=$cgroup_dev\n",
    "cgroup_ino=$cgroup_ino\n");
publish_exclusive("$o{owner_journal}.cgroup", $cgroup_text, 0600);
$cgroup_journal_owned = 1;
my @manifest_rows;
for my $name (sort keys %role_path) {
    push @manifest_rows, "role=$name path=$role_path{$name} sha256=$role_hash{$name}\n";
}
for my $entry (@stage2_helper_inventory) {
    my $name = $entry->[0];
    next unless exists $helper_path{$name};
    push @manifest_rows, "helper=$name path=$helper_path{$name} " .
        "dev=$helper_dev{$name} ino=$helper_ino{$name} sha256=$helper_hash{$name}\n";
}
my $launch_plan = join('',
    "schema=simple-stage3-unit-launch-plan-v2\n", "status=ready\n",
    "architecture=$o{architecture}\n", "run_id=$o{run_id}\n",
    "phase=$o{phase}\n", "unit=$unit\n", "memory_max_bytes=$o{memory_max}\n",
    "memory_swap_max_bytes=0\n", "memory_oom_group=1\n",
    "runtime_max_sec=3900\n", "exit_type=cgroup\n", "oom_policy=kill\n",
    "kill_mode=control-group\n", "send_sigkill=yes\n",
    "cgroup_dev=$cgroup_dev\n", "cgroup_ino=$cgroup_ino\n",
    "systemd_run_sha256=" . hash_fh($o{systemd_run_fh}) . "\n",
    "systemctl_sha256=" . hash_fh($o{systemctl_fh}) . "\n",
    "environment_sha256=" . vector_hash(@env) . "\n",
    "payload_argv_sha256=" . vector_hash(@payload) . "\n", @manifest_rows);
publish_exclusive("$o{evidence}/launch-plan.env", $launch_plan, 0600);
test_barrier('cgroup-ready');
length($interrupted) and die "supervisor interrupted by $interrupted\n";

print {$gate_w} 'G' or die "release pre-exec gate: $!\n";
close($gate_w) or die "close pre-exec gate: $!\n";
my $service_status = wait_bounded($systemd_pid, $o{service_timeout_ms});
if (!defined($service_status) || length($interrupted)) {
    stop_and_reap_unit();
    die(length($interrupted) ? "supervisor interrupted by $interrupted\n" : "service timeout\n");
}
undef $systemd_pid;

my $zero_deadline = now_ms() + $o{stop_timeout_ms};
while (now_ms() < $zero_deadline && !prove_held_cgroup_empty()) { sleep(0.01); }
my $active = systemctl_value('ActiveState');
defined($active) && $active eq 'inactive' or die "unit is not inactive\n";
prove_held_cgroup_empty() or die "held cgroup is not empty\n";
my %events_after = parse_counter_file(read_all($cgfd{'memory.events'}));
my %delta;
for my $key (qw(max oom oom_kill oom_group_kill)) {
    exists($events_after{$key}) && $events_after{$key} >= $events_before{$key}
        or die "memory.events counter invalid for $key\n";
    $delta{$key} = $events_after{$key} - $events_before{$key};
    $delta{$key} == 0 or die "memory.events delta is positive for $key\n";
}
my $swap_after = read_all($cgfd{'memory.swap.current'}); $swap_after =~ s/\s+\z//;
$swap_after eq '0' or die "terminal swap is nonzero\n";
my $peak = read_all($cgfd{'memory.peak'}); $peak =~ s/\s+\z//;
$peak =~ /\A[0-9]+\z/ && $peak < $o{memory_max}
    or die "memory peak reached or exceeded cap\n";
if ($o{phase} eq 'stage2') {
    my $transaction = open_directory($stage2_transaction_root);
    my $transaction_path = '/proc/self/fd/' . fileno($transaction);
    opendir(my $entries, $transaction_path)
        or die "enumerate Stage 2 transaction: $!\n";
    my @entry = sort grep { $_ ne '.' && $_ ne '..' } readdir($entries);
    closedir($entries) or die "close Stage 2 transaction enumeration: $!\n";
    join("\0", @entry) eq
        join("\0", qw(cache evidence home output tmp transaction.env))
        or die "Stage 2 transaction has non-canonical children\n";

    sysopen(my $receipt, "$transaction_path/transaction.env",
        O_RDONLY | O_NOFOLLOW | $O_CLOEXEC)
        or die "open Stage 2 transaction receipt: $!\n";
    my (%single, %receipt_helper, %receipt_child);
    for my $line (split /\n/, read_all($receipt)) {
        next if $line eq '';
        if ($line =~ /\Ahelper=([a-z][a-z0-9_]*) dev=([0-9]+) ino=([1-9][0-9]*) sha256=([0-9a-f]{64})\z/) {
            !exists($receipt_helper{$1})
                or die "duplicate Stage 2 helper receipt $1\n";
            $receipt_helper{$1} = [$2, $3, $4];
        } elsif ($line =~ /\Achild=(output|evidence|home|tmp|cache) dev=([0-9]+) ino=([1-9][0-9]*) content_sha256=([0-9a-f]{64})\z/) {
            !exists($receipt_child{$1})
                or die "duplicate Stage 2 child receipt $1\n";
            $receipt_child{$1} = [$2, $3, $4];
        } elsif ($line =~ /\A([a-z][a-z0-9_]*)=(.*)\z/s) {
            !exists($single{$1})
                or die "duplicate Stage 2 transaction key $1\n";
            $single{$1} = $2;
        } else {
            die "malformed Stage 2 transaction receipt row\n";
        }
    }
    close($receipt) or die "close Stage 2 transaction receipt: $!\n";
    receipt_has_exact_keys(\%single, qw(schema status exit_code bootstrap_dev
            bootstrap_ino bootstrap_sha256 outcome outcome_sha256))
        or die "Stage 2 transaction receipt key mismatch\n";
    $single{schema} eq 'simple-bootstrap-stage2-transaction-v1' &&
        $single{status} eq 'committed' &&
        $single{exit_code} =~ /\A[0-9]+\z/ &&
        $single{exit_code} == $service_status &&
        $single{bootstrap_dev} eq "$stage2_bootstrap_dev" &&
        $single{bootstrap_ino} eq "$stage2_bootstrap_ino" &&
        $single{bootstrap_sha256} eq $stage2_bootstrap_hash &&
        $single{outcome} eq 'evidence/result.env'
        or die "Stage 2 transaction authority mismatch\n";
    for my $entry (@stage2_helper_inventory) {
        my $name = $entry->[0];
        exists($receipt_helper{$name}) &&
            $receipt_helper{$name}[0] eq "$helper_dev{$name}" &&
            $receipt_helper{$name}[1] eq "$helper_ino{$name}" &&
            $receipt_helper{$name}[2] eq $helper_hash{$name}
            or die "Stage 2 helper receipt mismatch for $name\n";
        delete $receipt_helper{$name};
    }
    !keys(%receipt_helper) or die "unexpected Stage 2 helper receipt\n";
    for my $name (qw(output evidence home tmp cache)) {
        my $child = open_child_directory_fh(
            $transaction, $name, "Stage 2 child $name");
        my @identity = stat($child);
        my $hash = hash_stage2_directory($child, "Stage 2 child $name");
        exists($receipt_child{$name}) &&
            $receipt_child{$name}[0] eq "$identity[0]" &&
            $receipt_child{$name}[1] eq "$identity[1]" &&
            $receipt_child{$name}[2] eq $hash
            or die "Stage 2 child receipt mismatch for $name\n";
        delete $receipt_child{$name};
        close($child) or die "close Stage 2 child $name: $!\n";
    }
    !keys(%receipt_child) or die "unexpected Stage 2 child receipt\n";
    sysopen(my $outcome, "$transaction_path/evidence/result.env",
        O_RDONLY | O_NOFOLLOW | $O_CLOEXEC)
        or die "open Stage 2 outcome receipt: $!\n";
    my $outcome_text = read_all($outcome);
    close($outcome) or die "close Stage 2 outcome receipt: $!\n";
    sha256_hex($outcome_text) eq $single{outcome_sha256}
        or die "Stage 2 outcome receipt hash mismatch\n";
    my %outcome_row;
    for my $line (split /\n/, $outcome_text, -1) {
        next if $line eq '';
        $line =~ /\A([a-z][a-z0-9_]*)=(.*)\z/s
            or die "malformed Stage 2 outcome receipt row\n";
        !exists($outcome_row{$1})
            or die "duplicate Stage 2 outcome receipt key $1\n";
        $outcome_row{$1} = $2;
    }
    receipt_has_exact_keys(\%outcome_row, qw(schema status exit_code
            compiler_wall_ms wall_scope jobs memory_max_bytes memory_authority
            lock_authority descendant_cleanup_authority runner_zero_proof))
        or die "Stage 2 outcome receipt key mismatch\n";
    $outcome_row{schema} eq 'simple-bootstrap-stage2-runner-v4' &&
        $outcome_row{status} eq ($service_status == 0 ? 'succeeded' : 'failed') &&
        $outcome_row{exit_code} =~ /\A[0-9]+\z/ &&
        $outcome_row{exit_code} == $service_status &&
        $outcome_row{exit_code} == $single{exit_code} &&
        $outcome_row{wall_scope} eq 'stage2-compiler-native-build-only' &&
        $outcome_row{jobs} eq '16' &&
        $outcome_row{memory_max_bytes} eq '53687091200' &&
        $outcome_row{memory_authority} eq 'outer-supervisor' &&
        $outcome_row{lock_authority} eq
            'outer-supervisor-descriptor-verified' &&
        $outcome_row{descendant_cleanup_authority} eq 'outer-cgroup' &&
        $outcome_row{runner_zero_proof} eq 'not-claimed'
        or die "Stage 2 outcome/service authority mismatch\n";
    close($transaction) or die "close Stage 2 transaction: $!\n";
}
$service_status == 0 or die "systemd-run failed with status $service_status\n";

unlink_durable("$o{owner_journal}.cgroup");
$cgroup_journal_owned = 0;
unlink_durable($o{owner_journal});
$journal_owned = 0;
$unit_spawned = 0;
$cleanup_armed = 0;
for my $name (sort keys %cgfd) {
    close($cgfd{$name}) or die "close held cgroup file $name: $!\n";
}
close($cgroup_fh) or die "close held cgroup directory: $!\n";
undef $cgroup_fh;
for my $name (sort keys %role_fh) {
    close($role_fh{$name}) or die "close held role descriptor $name: $!\n";
}
for my $name (sort keys %helper_fh) {
    close($helper_fh{$name}) or die "close held helper descriptor $name: $!\n";
}
close($o{systemd_run_fh}) or die "close systemd-run descriptor: $!\n";
close($o{systemctl_fh}) or die "close systemctl descriptor: $!\n";
close($root_fh) or die "close root descriptor: $!\n";
undef $root_fh;
my $terminal = join('',
    "schema=simple-stage3-unit-terminal-v2\n", "status=pass\n",
    "architecture=$o{architecture}\n", "run_id=$o{run_id}\n",
    "phase=$o{phase}\n", "unit=$unit\n", "systemd_exit=$service_status\n",
    "working_directory_authority=descriptor-pinned-root\n",
    "heavy_lock_capability=" . ($o{phase} eq 'stage2' ?
        'supervisor-locked-ofd-via-systemd-pipe-gate-fd9' :
        'supervisor-only') . "\n",
    "active_state=inactive\n", "populated=0\n", "cgroup_dev=$cgroup_dev\n",
    "cgroup_ino=$cgroup_ino\n", "memory_peak_bytes=$peak\n",
    "memory_max_delta=$delta{max}\n", "memory_oom_delta=$delta{oom}\n",
    "memory_oom_kill_delta=$delta{oom_kill}\n",
    "memory_oom_group_kill_delta=$delta{oom_group_kill}\n",
    "memory_swap_current_terminal_bytes=0\n", "cleanup=inactive-populated-zero\n");
my $terminal_path = "$o{evidence}/terminal.env";
my $terminal_prepared =
    "$o{evidence}/.terminal.env.prepared.$o{run_id}";
publish_exclusive($terminal_prepared, $terminal, 0600);
test_barrier('terminal-prepared');
length($interrupted) and die "supervisor interrupted by $interrupted\n";
my @terminal_stat = lstat($terminal_prepared);
@terminal_stat && -f _ or die "prepared terminal is not regular\n";
my $terminal_commit = join('',
    "schema=simple-stage3-unit-terminal-commit-v1\n", "status=prepared\n",
    "architecture=$o{architecture}\n", "run_id=$o{run_id}\n",
    "phase=$o{phase}\n", "unit=$unit\n",
    "terminal_sha256=" . sha256_hex($terminal) . "\n",
    "terminal_dev=$terminal_stat[0]\n", "terminal_ino=$terminal_stat[1]\n");
my $terminal_commit_path =
    "$o{evidence}/.terminal.env.commit.$o{run_id}";
publish_exclusive($terminal_commit_path, $terminal_commit, 0600,
    'terminal-commit');
test_barrier('terminal-commit-durable');
length($interrupted) and die "supervisor interrupted by $interrupted\n";
flock($lock_fh, LOCK_UN) or die "unlock heavy lock: $!\n";
close($lock_fh) or die "close heavy lock: $!\n";
undef $lock_fh;
link($terminal_prepared, $terminal_path)
    or die "terminal publication collision: $!\n";
# The no-replace hard link is deliberately the final fallible operation.  A
# consumer accepts it only with the already durable, exact non-PASS commit
# receipt whose hash and inode identity match this terminal.  A crash can lose
# the final link (a recoverable HOLD) but cannot expose an accepted false PASS.
POSIX::_exit(0);
