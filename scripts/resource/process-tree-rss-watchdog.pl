#!/usr/bin/perl
# Sampled protection only. Ordinary compile acceptance remains <1,000,000,000 bytes.
# ps reports KiB on macOS and Linux. Keep one supervisor alive at 100 ms;
# do not fork a shell/awk/sleep pipeline for every sample.
use strict;
use warnings;
use POSIX qw(setsid setpgid WNOHANG);
use Time::HiRes qw(time sleep alarm);
use Cwd qw(abs_path);
use File::Basename qw(dirname);
use File::Temp qw(tempdir);
use Fcntl qw(O_RDONLY O_NOFOLLOW);
use Digest::SHA;

my %opt = ( 'max-rss-kib' => 5859375, 'interval-ms' => 100,
            'timeout-seconds' => 0, 'term-grace-seconds' => 1, 'session-mode' => 'new' );
while (@ARGV && $ARGV[0] ne '--') {
    my $arg = shift @ARGV;
    $arg =~ /^--(max-rss-kib|interval-ms|timeout-seconds|term-grace-seconds|receipt|session-mode)=(.+)$/
        or die "rss-guard: invalid option\n";
    $opt{$1} = $2;
}
@ARGV > 1 && shift(@ARGV) eq '--' or die "rss-guard: missing command\n";
$opt{'session-mode'} =~ /\A(?:new|inherit)\z/ or die "rss-guard: invalid session mode\n";
for my $key (qw(max-rss-kib interval-ms timeout-seconds term-grace-seconds)) {
    $opt{$key} =~ /^\d+$/ or die "rss-guard: invalid $key\n";
}
$opt{'max-rss-kib'} > 0 && $opt{'max-rss-kib'} <= 5859375
    or die "rss-guard: cap must be between 1 and 5859375 KiB (6000000000 bytes)\n";
$opt{'interval-ms'} > 0 && $opt{'interval-ms'} <= 100
    or die "rss-guard: sample interval must be between 1 and 100 ms\n";
my $leader = 0;
my %known;
my %groups;
my $identity_lost = 0;
my ($peak, $samples, $child_status, $interrupted);
$peak = $samples = $interrupted = 0;
my $started = time;
my $last = {};
my $ps_pid = 0;
my ($previous_sample, $sample_gap_max_ms) = (0, 0);
my ($session_helper, $helper_sha, $helper_source_sha, $helper_fd);
my ($session_id, $session_checks, $helper_failed, $helper_installed) = (0, 0, 0, 0);
my $session_root_confirmed = 0;
my ($session_admission, $parent_admission_sha) = ('', '');
my %unexpected_sid;
my $sample_started_at;
# The cadence is a scheduling target, not a deadline for a host-wide process
# observation. Keep slow but valid samples bounded separately from that target.
my $observation_budget_ms = 1000;
my ($sample_duration_max_ms, $sample_overruns) = (0, 0);

sub hash_handle {
    my ($fh) = @_;
    seek($fh, 0, 0) or die "cannot seek session helper";
    return Digest::SHA->new(256)->addfile($fh)->hexdigest;
}

sub verify_session_helper {
    my @path = lstat($session_helper);
    my @pinned = stat($helper_fd);
    if (!@path || !@pinned || -l $session_helper || $path[0] != $pinned[0] ||
        $path[1] != $pinned[1] || hash_handle($helper_fd) ne $helper_sha) {
        $helper_failed = 1;
        die "session helper identity/hash changed";
    }
}

sub observe_sessions {
    my ($budget, @pids) = @_;
    verify_session_helper();
    return {} unless @pids;
    $budget > 0 or die "session observation exceeded observation budget";
    my %expected = map { $_ => 1 } @pids;
    my %result;
    my $observer = open(my $fh, '-|', $session_helper, '--sid', @pids);
    defined($observer) or die "cannot start session observer";
    local $SIG{ALRM} = sub { kill 'KILL', $observer; die "session observation timed out" };
    alarm($budget);
    while (my $line = <$fh>) {
        $line =~ /\A([0-9]+) ([0-9]+)\n\z/ or die "malformed session observation";
        my ($pid, $sid) = ($1, $2);
        delete($expected{$pid}) or die "unexpected/repeated session PID";
        $result{$pid} = $sid;
        ++$session_checks;
    }
    close($fh) or die "session observer failed";
    alarm 0;
    !%expected or die "incomplete session observation";
    verify_session_helper();
    return \%result;
}

sub install_session_helper {
    my $has_id = exists($ENV{SIMPLE_BOOTSTRAP_SESSION_ID});
    my $has_exec = exists($ENV{SIMPLE_BOOTSTRAP_SESSION_EXEC});
    if ($opt{'session-mode'} eq 'new') {
        !$has_id && !$has_exec or die "new session refuses inherited session contract";
    } else {
        $has_id && $has_exec or die "incomplete inherited session contract";
    }
    my $source = abs_path(dirname(__FILE__) . '/../bootstrap/bootstrap-session-exec.c');
    defined($source) or die "missing session helper source";
    open(my $source_fh, '<', $source) or die "cannot read session helper source";
    $helper_source_sha = hash_handle($source_fh);
    my $directory = defined($opt{receipt}) ?
        tempdir('simple-rss-session-XXXXXXXX', DIR => dirname($opt{receipt}), CLEANUP => 0) :
        tempdir('simple-rss-session-XXXXXXXX', TMPDIR => 1, CLEANUP => 0);
    $directory = abs_path($directory);
    $session_helper = "$directory/bootstrap-session-exec";
    my $compiler = $ENV{CC} || 'cc';
    my $builder = fork();
    defined($builder) or die "cannot fork helper compiler";
    if (!$builder) {
        setpgid(0, 0) == 0 or POSIX::_exit(89);
        exec {$compiler} $compiler, '-O2', $source, '-o', $session_helper or POSIX::_exit(127);
    }
    my $deadline = time + 30;
    while (1) {
        my $done = waitpid($builder, WNOHANG);
        if ($done == $builder) { $? == 0 or die "session helper compilation failed"; last }
        if (time >= $deadline) {
            # The direct compiler child is still unreaped and anchors its group.
            kill 'KILL', -$builder;
            kill 'KILL', $builder;
            waitpid($builder, 0);
            die "session helper compilation timed out";
        }
        sleep 0.02;
    }
    hash_handle($source_fh) eq $helper_source_sha or die "session helper source changed during compilation";
    close($source_fh);
    chmod(0500, $session_helper) == 1 or die "cannot protect session helper";
    sysopen($helper_fd, $session_helper, O_RDONLY | O_NOFOLLOW) or die "cannot pin session helper";
    -f $helper_fd or die "session helper is not a regular file";
    $helper_sha = hash_handle($helper_fd);
    # Cold Darwin executable admission can exceed two seconds under host load.
    # No workload exists yet: allow one bounded warmup, while snapshot() keeps
    # a separate bounded observation deadline after workload creation.
    my $own_sid = observe_sessions(5, $$)->{$$};
    $own_sid > 0 or die "cannot determine supervisor session";
    if ($opt{'session-mode'} eq 'inherit') {
        $ENV{SIMPLE_BOOTSTRAP_SESSION_ID} =~ /\A[1-9][0-9]*\z/ &&
            $ENV{SIMPLE_BOOTSTRAP_SESSION_ID} == $own_sid &&
            $ENV{SIMPLE_BOOTSTRAP_SESSION_EXEC} =~ m{\A/} &&
            -f $ENV{SIMPLE_BOOTSTRAP_SESSION_EXEC} or die "invalid inherited session contract";
        my $parent_helper = $ENV{SIMPLE_BOOTSTRAP_SESSION_EXEC};
        sysopen(my $admission, "$parent_helper.admission.env", O_RDONLY | O_NOFOLLOW)
            or die "missing inherited session admission";
        my @admission_stat = stat($admission);
        -f $admission && $admission_stat[4] == $< && ($admission_stat[2] & 0777) == 0400
            or die "unsafe inherited session admission";
        $parent_admission_sha = hash_handle($admission);
        seek($admission, 0, 0) or die "cannot read inherited session admission";
        my %admitted;
        while (my $line = <$admission>) {
            $line =~ /\A([a-z_]+)=([^\n]*)\n\z/ or die "malformed inherited session admission";
            !exists($admitted{$1}) or die "duplicate inherited session admission field";
            $admitted{$1} = $2;
        }
        ($admitted{schema} || '') eq 'simple-bootstrap-session-v1' &&
            ($admitted{status} || '') eq 'active' &&
            ($admitted{session_id} || '') eq "$own_sid" &&
            ($admitted{session_helper} || '') eq $parent_helper &&
            ($admitted{session_helper_source_sha} || '') eq $helper_source_sha &&
            ($admitted{root_pid} || '') =~ /\A[1-9][0-9]*\z/
            or die "inherited session admission mismatch";
        sysopen(my $parent_binary, $parent_helper, O_RDONLY | O_NOFOLLOW)
            or die "cannot pin inherited session helper";
        -f $parent_binary && hash_handle($parent_binary) eq ($admitted{session_helper_sha} || '')
            or die "inherited session helper hash mismatch";
        my $parent_sid = observe_sessions(2, $admitted{root_pid})->{$admitted{root_pid}};
        $parent_sid == $own_sid or die "inherited root is absent or escaped";
        hash_handle($admission) eq $parent_admission_sha or die "inherited admission changed";
        $session_id = $own_sid;
    }
    $helper_installed = 1;
}

sub publish_session_admission {
    $session_admission = "$session_helper.admission.env";
    my $temporary = "$session_admission.tmp.$$";
    open(my $fh, '>', $temporary) or die "cannot create session admission";
    print $fh "schema=simple-bootstrap-session-v1\nstatus=active\nroot_pid=$leader\n" .
        "session_id=$session_id\nsession_helper=$session_helper\n" .
        "session_helper_sha=$helper_sha\nsession_helper_source_sha=$helper_source_sha\n";
    close($fh) && chmod(0400, $temporary) && rename($temporary, $session_admission)
        or die "cannot publish session admission";
}

sub snapshot {
    $sample_started_at = time;
    local $ENV{LC_ALL} = 'C';
    # List form bypasses shell pipelines, so a failing ps cannot be hidden by awk.
    $ps_pid = open(my $ps, '-|', 'ps', '-axo', 'pid=,ppid=,pgid=,rss=,stat=,lstart=');
    defined($ps_pid) or die "cannot start ps";
    my %all;
    local $SIG{ALRM} = sub { kill 'KILL', $ps_pid; die "ps timed out" };
    alarm($observation_budget_ms / 1000);
    while (my $line = <$ps>) {
        $line =~ /^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\S+)\s+(.+?)\s*$/
            or die "malformed ps row";
        my ($pid, $parent, $group, $rss, $state, $identity) = ($1,$2,$3,$4,$5,$6);
        $all{$pid} = { parent => 0+$parent, group => 0+$group, rss => 0+$rss,
                     zombie => scalar($state =~ /^Z/), identity => $identity };
    }
    close($ps) or die "ps failed";
    alarm 0;
    %all or die "empty ps output";
    ++$samples;
    if ($leader && defined($session_helper) && !$helper_failed &&
        ($session_root_confirmed || (exists($all{$leader}) && $all{$leader}{group} == $leader))) {
        my @live = members(\%all);
        my $remaining = $observation_budget_ms / 1000 - (time - $sample_started_at);
        my $sids = observe_sessions($remaining, @live);
        $session_root_confirmed = 1 if ($sids->{$leader} || 0) == $session_id;
        for my $id (keys %$sids) {
            $unexpected_sid{$id} = $sids->{$id} if $sids->{$id} && $sids->{$id} != $session_id;
        }
    }
    my $duration_ms = (time - $sample_started_at) * 1000;
    $duration_ms <= $observation_budget_ms or die "process observation exceeded observation budget";
    $sample_duration_max_ms = $duration_ms if $duration_ms > $sample_duration_max_ms;
    ++$sample_overruns if $duration_ms > $opt{'interval-ms'};
    return \%all;
}

sub members {
    my ($all) = @_;
    for my $group (keys %groups) {
        my @current = grep { $all->{$_}{group} == $group } keys %$all;
        my $anchor = exists($all->{$group}) &&
            $all->{$group}{identity} eq $groups{$group};
        my $continuity = grep { exists($known{$_}) &&
            $known{$_} eq $all->{$_}{identity} } @current;
        if ((!$anchor && !$continuity) ||
            (exists($all->{$group}) && $all->{$group}{identity} ne $groups{$group})) {
            $identity_lost = 1 if @current;
            delete $groups{$group};
        }
    }
    my %selected;
    for my $pid (keys %$all) {
        $selected{$pid} = 1 if $pid == $leader || $all->{$pid}{group} == $leader ||
            $groups{$all->{$pid}{group}} ||
            (exists($known{$pid}) && $known{$pid} eq $all->{$pid}{identity});
    }
    my $changed = 1;
    while ($changed) {
        $changed = 0;
        for my $pid (keys %$all) {
            if (!$selected{$pid} && $selected{$all->{$pid}{parent}}) {
                $selected{$pid} = 1; $changed = 1;
            }
        }
    }
    delete $selected{$$};
    for my $pid (keys %selected) {
        $known{$pid} = $all->{$pid}{identity};
        # Retain observed session/group leaders as well as PIDs. A member may
        # fork between measurement and STOP; its child's group survives reparent.
        $groups{$pid} = $all->{$pid}{identity} if $all->{$pid}{group} == $pid;
    }
    return grep { !$all->{$_}{zombie} } keys %selected;
}

sub reap {
    return if defined $child_status;
    my $got = waitpid($leader, WNOHANG);
    $child_status = $? if $got == $leader;
}

sub signal_verified {
    my ($signal, $all) = @_;
    my @live = members($all);
    # A negative group signal requires a still-observed leader identity. When
    # a group leader is gone, signal only individually validated descendants.
    for my $group (keys %groups) {
        next unless exists($all->{$group}) &&
            $all->{$group}{identity} eq $groups{$group};
        kill $signal, -$group;
    }
    kill $signal, @live if @live;
    return @live;
}

sub quiesce {
    my $empty = 0;
    for (1..100) {
        my $all = eval { snapshot() };
        if (!$all) {
            alarm 0;
            # The direct child is not reaped until all signaling is finished,
            # so its PID anchors this group even when measurement is unavailable.
            # No cached escaped PID or PGID is safe to signal without validation.
            kill 'KILL', -$leader;
            kill 'KILL', $leader;
            return 0;
        }
        my @live = signal_verified('STOP', $all);
        if (@live) {
            # Discover children forked just before STOP while their parents
            # remain alive/frozen, before KILL can reparent them.
            my $frozen = eval { snapshot() };
            if (!$frozen) {
                alarm 0;
                kill 'KILL', -$leader;
                kill 'KILL', $leader;
                return 0;
            }
            signal_verified('KILL', $frozen);
        }
        $empty = @live ? 0 : $empty + 1;
        return !$identity_lost if $empty >= 3;
        sleep 0.02;
    }
    return 0;
}

sub receipt {
    my ($status, $code, $quiet) = @_;
    my $body = "status=$status\nexit_status=$code\nroot_pid=$leader\n" .
        "max_rss_kib=$opt{'max-rss-kib'}\npeak_rss_kib=$peak\nsamples=$samples\n" .
        "interval_ms=$opt{'interval-ms'}\nsample_gap_max_ms=$sample_gap_max_ms\n" .
        "observation_budget_ms=$observation_budget_ms\n" .
        "sample_duration_max_ms=$sample_duration_max_ms\nsample_overruns=$sample_overruns\n" .
        "containment_scope=observed-descendants-and-process-groups\n" .
        "hard_memory_limit=0\nquiescent=$quiet\n" .
        "session_id=$session_id\nsession_checks=$session_checks\n" .
        "session_mode=$opt{'session-mode'}\nsession_admission=$session_admission\n" .
        "parent_session_admission_sha256=$parent_admission_sha\n" .
        "ordinary_compile_rss_target_bytes=1000000000\n" .
        "session_helper=" . ($session_helper // '') . "\n" .
        "session_helper_sha256=" . ($helper_sha // '') . "\n" .
        "session_helper_source_sha256=" . ($helper_source_sha // '') . "\n" .
        "session_helper_integrity=" . ($helper_failed ? 'failed' : $helper_installed ? 'verified' : 'unverified') . "\n" .
        "unexpected_session_pids=" . join(',', sort {$a <=> $b} keys %unexpected_sid) . "\n";
    print STDERR $body if $code == 88 || $code == 89 || $code == 90;
    if (defined $opt{receipt}) {
        my $tmp = "$opt{receipt}.tmp.$$";
        open(my $fh, '>', $tmp) or die "rss-guard: cannot write receipt\n";
        print $fh $body;
        close($fh) && rename($tmp, $opt{receipt}) or die "rss-guard: cannot publish receipt\n";
    }
}

# Workload startup boundary (identity unit tests exercise functions above it).
if (!eval { install_session_helper(); 1 }) {
    alarm 0;
    warn "rss-guard: session installation failed: $@\n";
    receipt('session-helper-install-failed', 89, 1);
    exit 89;
}
$started = time;
pipe(my $gate_read, my $gate_write) or die "rss-guard: pipe failed\n";
$leader = fork();
defined($leader) or die "rss-guard: fork failed\n";
if ($leader == 0) {
    close $gate_write;
    if ($session_id) { setpgid(0, 0) == 0 or POSIX::_exit(89) }
    else { defined(setsid()) && getpgrp() == $$ or POSIX::_exit(89) }
    $ENV{SIMPLE_BOOTSTRAP_SESSION_ID} = $session_id || $$;
    $ENV{SIMPLE_BOOTSTRAP_SESSION_EXEC} = $session_helper;
    my $go;
    sysread($gate_read, $go, 1) == 1 && $go eq 'G' or POSIX::_exit(89);
    close $gate_read;
    exec { $ARGV[0] } @ARGV or POSIX::_exit(127);
}
close $gate_read;
$session_id ||= $leader;
$SIG{TERM} = sub { $interrupted = 143 };
$SIG{INT} = sub { $interrupted = 130 };
$SIG{HUP} = sub { $interrupted = 129 };
$SIG{PIPE} = 'IGNORE';
my ($status, $code) = ('complete', 0);
my $released = 0;
while (1) {
    my $sample_started = time;
    my $gap = $previous_sample ? ($sample_started - $previous_sample) * 1000 : 0;
    $sample_gap_max_ms = $gap if $gap > $sample_gap_max_ms;
    $previous_sample = $sample_started;
    my $all = eval { snapshot() };
    if (!$all) {
        alarm 0;
        warn "rss-guard: measurement failed: $@\n";
        ($status, $code) = ($helper_failed ? 'session-helper-invalid' : 'rss-measurement-failed', 89); last;
    }
    $last = $all;
    if (%unexpected_sid) { ($status, $code) = ('bootstrap-session-escaped', 90); last }
    my @live = members($all);
    my $rss = 0; $rss += $all->{$_}{rss} for @live;
    $peak = $rss if $rss > $peak;
    if ($rss >= $opt{'max-rss-kib'}) {
        ($status, $code) = ('rss-cap-exceeded', 88); last;
    }
    if (!$released) {
        # Both successful sampling and confirmed session isolation are required
        # before releasing exec. A child failure cannot launch unguarded work.
        if (exists($all->{$leader}) && $all->{$leader}{group} == $leader && $session_root_confirmed) {
            if (!eval { publish_session_admission(); 1 }) {
                ($status, $code) = ('session-admission-failed', 89); last;
            }
            syswrite($gate_write, 'G', 1) == 1 or do {
                ($status, $code) = ('rss-startup-failed', 89); last;
            };
            close $gate_write;
            $released = 1;
        } elsif (time - $started >= 2) {
            ($status, $code) = ('rss-startup-failed', 89); last;
        }
    }
    if ($interrupted) { ($status, $code) = ('interrupted', $interrupted); last }
    if ($opt{'timeout-seconds'} && time - $started >= $opt{'timeout-seconds'}) {
        ($status, $code) = ('timeout', 124); last;
    }
    # Keep the direct child unreaped as the root PGID identity anchor. A
    # zombie is completion evidence; obtain its exact wait status after cleanup.
    last if exists($all->{$leader}) && $all->{$leader}{zombie};
    my $remaining = $opt{'interval-ms'} / 1000 - (time - $sample_started);
    sleep($remaining) if $remaining > 0;
}
close $gate_write unless $released;
if ($code == 124 || $interrupted) {
    # Preserve the timeout wrapper's TERM/grace contract for artifact flushing.
    # RSS breaches use immediate STOP/KILL because allocations must stop.
    my $term_snapshot = eval { snapshot() };
    if ($term_snapshot) { signal_verified('TERM', $term_snapshot) }
    else { alarm 0; ($status, $code) = ('rss-measurement-failed', 89) }
    my $grace_end = time + $opt{'term-grace-seconds'};
    while (time < $grace_end) {
        my $all = eval { snapshot() };
        if (!$all) { alarm 0; ($status, $code) = ('rss-measurement-failed', 89); last }
        my @live = members($all);
        last unless @live;
        my $rss = 0; $rss += $all->{$_}{rss} for @live;
        $peak = $rss if $rss > $peak;
        if ($rss >= $opt{'max-rss-kib'}) { ($status, $code) = ('rss-cap-exceeded', 88); last }
        sleep 0.02;
    }
}
my $quiet = quiesce();
for (1..100) { reap(); last if defined $child_status; sleep 0.02 }
if ($status eq 'complete' && defined $child_status) {
    $code = ($child_status & 127) ? 128 + ($child_status & 127) : $child_status >> 8;
}
$quiet = 0 unless defined $child_status;
if (!$quiet && $code != 89) { ($status, $code) = ('rss-containment-unverified', 89) }
receipt($status, $code, $quiet);
exit $code;
