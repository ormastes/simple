#!/usr/bin/perl
use strict;
use warnings;
use Config;
use Errno qw(EINTR ECHILD ESRCH EPERM EEXIST);
use Fcntl qw(O_RDWR O_WRONLY O_CREAT O_EXCL O_NOFOLLOW O_DIRECTORY O_RDONLY F_SETFD FD_CLOEXEC);
use IO::Select;
use POSIX qw(WNOHANG setsid SIGTERM SIGINT SIGHUP SIGQUIT SIG_BLOCK SIG_SETMASK sigprocmask sigpending);
use Time::HiRes qw(time sleep);
use Digest::SHA qw(sha256_hex);

$SIG{__DIE__} = sub {
    print STDERR @_;
    # Normal exit runs END, which removes either unpublished temporary.
    exit(126);
};

my $SYS_RENAMEAT2 = $Config{archname} =~ /aarch64/ ? 276 :
    $Config{archname} =~ /x86_64/ ? 316 : undef;
defined($SYS_RENAMEAT2) or die "bounded-log-error: unsupported renameat2 architecture\n";
# renameat2 numbers are Linux ABI values. Fail closed rather than silently use
# pathname rename on an architecture not explicitly admitted above.
my $RENAME_NOREPLACE = 1;

my %option;
while (@ARGV && $ARGV[0] ne '--') {
    my $arg = shift @ARGV;
    $arg =~ /\A--([a-z-]+)=(.*)\z/ or die "bounded-log-error: invalid option\n";
    exists($option{$1}) and die "bounded-log-error: duplicate option\n";
    $option{$1} = $2;
}
@ARGV >= 2 && shift(@ARGV) eq '--' or die "bounded-log-error: missing command\n";
for my $key (qw(output-parent log-leaf receipt-leaf max-bytes timeout-seconds term-grace-seconds)) {
    exists($option{$key}) or die "bounded-log-error: missing option $key\n";
}
keys(%option) == 6 or die "bounded-log-error: unknown option\n";
$option{'output-parent'} =~ m{\A/proc/[1-9][0-9]*/fd/[1-9][0-9]*\z} or
    die "bounded-log-error: output parent is not a procfd descriptor\n";
for my $key (qw(log-leaf receipt-leaf)) {
    $option{$key} =~ /\A[A-Za-z0-9_.-]+\z/ &&
        $option{$key} ne '.' && $option{$key} ne '..' or
        die "bounded-log-error: unsafe $key\n";
}
$option{'log-leaf'} ne $option{'receipt-leaf'} or
    die "bounded-log-error: log and receipt leaves collide\n";
for my $key (qw(max-bytes timeout-seconds term-grace-seconds)) {
    $option{$key} =~ /\A[0-9]+\z/ or die "bounded-log-error: invalid $key\n";
}
$option{'max-bytes'} > 0 && $option{'timeout-seconds'} > 0 or
    die "bounded-log-error: nonpositive limit\n";

sysopen(my $parent, "$option{'output-parent'}/.",
    O_RDONLY | O_DIRECTORY | O_NOFOLLOW) or
    die "bounded-log-error: open output parent: $!\n";
my @parent_identity = stat($parent);
@parent_identity && -d _ or die "bounded-log-error: invalid output parent\n";
my $parent_ref = '/proc/self/fd/' . fileno($parent);
my $log_tmp_leaf = ".$option{'log-leaf'}.tmp.$$";
my $receipt_tmp_leaf = ".$option{'receipt-leaf'}.tmp.$$";
my $log_tmp_ref = "$parent_ref/$log_tmp_leaf";
my $receipt_tmp_ref = "$parent_ref/$receipt_tmp_leaf";
my ($log_tmp_created, $receipt_tmp_created) = (0, 0);
my ($log_published, $receipt_published) = (0, 0);
END {
    unlink($log_tmp_ref) if defined($log_tmp_ref) && $log_tmp_created && !$log_published;
    unlink($receipt_tmp_ref) if defined($receipt_tmp_ref) && $receipt_tmp_created && !$receipt_published;
}
# Test-only pause immediately before O_EXCL temp creation. The leaf remains
# derived solely from the supervisor PID; tests receive no naming override.
if (defined($ENV{BOUNDED_LOG_TEST_TEMP_READY_FD}) ||
        defined($ENV{BOUNDED_LOG_TEST_TEMP_ACK_FD})) {
    defined($ENV{BOUNDED_LOG_TEST_TEMP_READY_FD}) &&
        defined($ENV{BOUNDED_LOG_TEST_TEMP_ACK_FD}) &&
        $ENV{BOUNDED_LOG_TEST_TEMP_READY_FD} =~ /\A[0-9]+\z/ &&
        $ENV{BOUNDED_LOG_TEST_TEMP_ACK_FD} =~ /\A[0-9]+\z/ or
        die "bounded-log-error: invalid temp hook fds\n";
    open(my $temp_ready, '>&=', 0 + $ENV{BOUNDED_LOG_TEST_TEMP_READY_FD}) or
        die "bounded-log-error: open temp ready hook: $!\n";
    open(my $temp_ack, '<&=', 0 + $ENV{BOUNDED_LOG_TEST_TEMP_ACK_FD}) or
        die "bounded-log-error: open temp ack hook: $!\n";
    syswrite($temp_ready, 'T', 1) == 1 or die "bounded-log-error: temp hook write: $!\n";
    my $ack = '';
    while (length($ack) == 0) {
        my $count = sysread($temp_ack, $ack, 1);
        next if !defined($count) && $! == EINTR;
        defined($count) && $count == 1 or die "bounded-log-error: temp hook read: $!\n";
    }
    close($temp_ready) or die "bounded-log-error: close temp ready hook: $!\n";
    close($temp_ack) or die "bounded-log-error: close temp ack hook: $!\n";
}
sysopen(my $log, $log_tmp_ref, O_RDWR | O_CREAT | O_EXCL | O_NOFOLLOW, 0600)
    or die "bounded-log-error: create log temporary: $!\n";
$log_tmp_created = 1;

pipe(my $stream_r, my $stream_w) or die "bounded-log-error: stream pipe: $!\n";
pipe(my $ready_r, my $ready_w) or die "bounded-log-error: readiness pipe: $!\n";
pipe(my $exec_r, my $exec_w) or die "bounded-log-error: exec-status pipe: $!\n";
fcntl($exec_w, F_SETFD, FD_CLOEXEC) or die "bounded-log-error: exec-status cloexec: $!\n";
my $pid = fork();
defined($pid) or die "bounded-log-error: fork: $!\n";
if (!$pid) {
    close($stream_r); close($ready_r); close($exec_r);
    $SIG{HUP} = $SIG{INT} = $SIG{QUIT} = $SIG{TERM} = 'DEFAULT';
    setsid() >= 0 or POSIX::_exit(125);
    syswrite($ready_w, 'R', 1) == 1 or POSIX::_exit(125);
    close($ready_w);
    open(STDOUT, '>&', $stream_w) or POSIX::_exit(125);
    open(STDERR, '>&', $stream_w) or POSIX::_exit(125);
    close($stream_w);
    exec {$ARGV[0]} @ARGV or do {
        syswrite($exec_w, 'E', 1);
        POSIX::_exit(127);
    };
}
close($stream_w); close($ready_w); close($exec_w);

my ($caught, $reaped, $raw_wait) = ('', 0, 0);
$SIG{TERM} = sub { $caught ||= 'TERM' };
$SIG{INT} = sub { $caught ||= 'INT' };
$SIG{HUP} = sub { $caught ||= 'HUP' };
$SIG{QUIT} = sub { $caught ||= 'QUIT' };
my %signal_number = (HUP => SIGHUP, INT => SIGINT, QUIT => SIGQUIT, TERM => SIGTERM);

sub group_alive {
    my $sent = kill(0, -$pid);
    return 1 if $sent > 0 || $! == EPERM;
    return 0 if $! == ESRCH;
    die "bounded-log-error: process-group probe: $!\n";
}
sub observe_root {
    return if $reaped;
    my $seen = waitpid($pid, WNOHANG);
    if ($seen == $pid) { $raw_wait = $?; $reaped = 1; return; }
    return if $seen == 0;
    if ($seen == -1 && $! == ECHILD) { $reaped = 1; return; }
    die "bounded-log-error: waitpid: $!\n";
}
sub terminate_group {
    kill('TERM', -$pid) if group_alive();
    my $term_deadline = time() + $option{'term-grace-seconds'};
    while (time() < $term_deadline) {
        observe_root();
        last unless group_alive();
        sleep(0.01);
    }
    kill('KILL', -$pid) if group_alive();
    my $kill_deadline = time() + 10;
    while (time() < $kill_deadline) {
        observe_root();
        last if $reaped && !group_alive();
        sleep(0.01);
    }
    observe_root();
    $reaped or die "bounded-log-error: child reap deadline\n";
    group_alive() and die "bounded-log-error: process group survived cleanup\n";
}
sub write_all {
    my ($fh, $bytes) = @_;
    my $offset = 0;
    while ($offset < length($bytes)) {
        my $count = syswrite($fh, $bytes, length($bytes) - $offset, $offset);
        next if !defined($count) && $! == EINTR;
        defined($count) && $count > 0 or die "bounded-log-error: write: $!\n";
        $offset += $count;
    }
}

my $started = time();
my $deadline = $started + $option{'timeout-seconds'};
my $ready_select = IO::Select->new($ready_r);
my $ready = '';
while (!$caught && time() < $deadline && length($ready) == 0) {
    next unless $ready_select->can_read(0.05);
    my $count = sysread($ready_r, $ready, 1);
    next if !defined($count) && $! == EINTR;
    defined($count) or die "bounded-log-error: readiness read: $!\n";
    last if $count == 0;
}
close($ready_r);
my ($reason, $raw_status) = ('', 0);
if ($caught) { $reason = 'supervisor-signal'; terminate_group(); }
elsif ($ready ne 'R') { $reason = time() >= $deadline ? 'timeout' : 'setup-failure'; terminate_group(); }

my ($bytes_captured, $eof) = (0, 0);
my $stream_select = IO::Select->new($stream_r);
while (!$reason) {
    observe_root();
    last if $reaped && $eof && !group_alive();
    if ($caught) { $reason = 'supervisor-signal'; terminate_group(); last; }
    if (time() >= $deadline) { $reason = 'timeout'; terminate_group(); last; }
    if (!$eof && $stream_select->can_read(0.05)) {
        my $count = sysread($stream_r, my $bytes, 65_536);
        next if !defined($count) && $! == EINTR;
        defined($count) or die "bounded-log-error: stream read: $!\n";
        if ($count == 0) { $eof = 1; $stream_select->remove($stream_r); next; }
        if ($bytes_captured + $count > $option{'max-bytes'}) {
            my $remaining = $option{'max-bytes'} - $bytes_captured;
            write_all($log, substr($bytes, 0, $remaining)) if $remaining > 0;
            $bytes_captured += $remaining;
            $reason = 'overflow'; terminate_group(); last;
        }
        write_all($log, substr($bytes, 0, $count));
        $bytes_captured += $count;
    } elsif ($eof) { sleep(0.01); }
}
close($stream_r);
my $exec_state = '';
while (1) {
    my $count = sysread($exec_r, $exec_state, 1);
    next if !defined($count) && $! == EINTR;
    defined($count) or die "bounded-log-error: exec-status read: $!\n";
    last;
}
close($exec_r);
if (!$reason) {
    $raw_status = ($raw_wait & 127) ? 128 + ($raw_wait & 127) : ($raw_wait >> 8);
    $reason = $exec_state eq 'E' ? 'exec-failure' :
        ($raw_wait & 127) ? 'child-signal' : 'child-exit';
} elsif ($reason eq 'timeout') { $raw_status = 124; }
elsif ($reason eq 'overflow') { $raw_status = 125; }
elsif ($reason eq 'setup-failure') { $raw_status = 126; }
elsif ($reason eq 'supervisor-signal') { $raw_status = 128 + $signal_number{$caught}; }

$log->sync or die "bounded-log-error: fsync log: $!\n";
seek($log, 0, 0) or die "bounded-log-error: rewind log temporary: $!\n";
my $digest = Digest::SHA->new(256);
$digest->addfile($log);
my $log_sha256 = $digest->hexdigest;
close($log) or die "bounded-log-error: close log: $!\n";

# Test-only descriptor handshake. It makes the signal/publication race
# deterministic without sleeps; production leaves the variable unset.
if (defined($ENV{BOUNDED_LOG_TEST_PUBLICATION_READY_FD}) ||
        defined($ENV{BOUNDED_LOG_TEST_PUBLICATION_ACK_FD})) {
    defined($ENV{BOUNDED_LOG_TEST_PUBLICATION_READY_FD}) &&
        defined($ENV{BOUNDED_LOG_TEST_PUBLICATION_ACK_FD}) &&
        $ENV{BOUNDED_LOG_TEST_PUBLICATION_READY_FD} =~ /\A[0-9]+\z/ &&
        $ENV{BOUNDED_LOG_TEST_PUBLICATION_ACK_FD} =~ /\A[0-9]+\z/ or
        die "bounded-log-error: invalid publication hook fds\n";
    open(my $hook_ready, '>&=', 0 + $ENV{BOUNDED_LOG_TEST_PUBLICATION_READY_FD}) or
        die "bounded-log-error: open publication ready hook: $!\n";
    open(my $hook_ack, '<&=', 0 + $ENV{BOUNDED_LOG_TEST_PUBLICATION_ACK_FD}) or
        die "bounded-log-error: open publication ack hook: $!\n";
    syswrite($hook_ready, 'P', 1) == 1 or die "bounded-log-error: publication hook write: $!\n";
    my $ack = '';
    while (length($ack) == 0) {
        my $count = sysread($hook_ack, $ack, 1);
        next if !defined($count) && $! == EINTR;
        defined($count) && $count == 1 or die "bounded-log-error: publication hook read: $!\n";
    }
    close($hook_ready) or die "bounded-log-error: close publication ready hook: $!\n";
    close($hook_ack) or die "bounded-log-error: close publication ack hook: $!\n";
}
my $terminal_set = POSIX::SigSet->new(SIGTERM, SIGINT, SIGHUP, SIGQUIT);
my $old_set = POSIX::SigSet->new();
defined(sigprocmask(SIG_BLOCK, $terminal_set, $old_set)) or
    die "bounded-log-error: block publication signals: $!\n";
my $pending = POSIX::SigSet->new();
defined(sigpending($pending)) or die "bounded-log-error: inspect publication signals: $!\n";
if (!$caught) {
    $caught = 'TERM' if $pending->ismember(SIGTERM);
    $caught = 'INT' if !$caught && $pending->ismember(SIGINT);
    $caught = 'HUP' if !$caught && $pending->ismember(SIGHUP);
    $caught = 'QUIT' if !$caught && $pending->ismember(SIGQUIT);
}
if ($caught && $reason ne 'supervisor-signal') {
    $reason = 'supervisor-signal';
    $raw_status = 128 + $signal_number{$caught};
}
my $cancel_before_commit = $reason eq 'supervisor-signal';
# The pending check above is the publication linearization point. Signals
# arriving after it are deliberately kept blocked through process exit: they
# are ordered after the durable result and cannot rewrite its receipt/status.
if (defined($ENV{BOUNDED_LOG_TEST_LATE_SIGNAL_READY_FD}) ||
        defined($ENV{BOUNDED_LOG_TEST_LATE_SIGNAL_ACK_FD})) {
    defined($ENV{BOUNDED_LOG_TEST_LATE_SIGNAL_READY_FD}) &&
        defined($ENV{BOUNDED_LOG_TEST_LATE_SIGNAL_ACK_FD}) &&
        $ENV{BOUNDED_LOG_TEST_LATE_SIGNAL_READY_FD} =~ /\A[0-9]+\z/ &&
        $ENV{BOUNDED_LOG_TEST_LATE_SIGNAL_ACK_FD} =~ /\A[0-9]+\z/ or
        die "bounded-log-error: invalid late-signal hook fds\n";
    open(my $late_ready, '>&=', 0 + $ENV{BOUNDED_LOG_TEST_LATE_SIGNAL_READY_FD}) or
        die "bounded-log-error: open late-signal ready hook: $!\n";
    open(my $late_ack, '<&=', 0 + $ENV{BOUNDED_LOG_TEST_LATE_SIGNAL_ACK_FD}) or
        die "bounded-log-error: open late-signal ack hook: $!\n";
    syswrite($late_ready, 'L', 1) == 1 or die "bounded-log-error: late-signal hook write: $!\n";
    my $ack = '';
    while (length($ack) == 0) {
        my $count = sysread($late_ack, $ack, 1);
        next if !defined($count) && $! == EINTR;
        defined($count) && $count == 1 or die "bounded-log-error: late-signal hook read: $!\n";
    }
    close($late_ready) or die "bounded-log-error: close late-signal ready hook: $!\n";
    close($late_ack) or die "bounded-log-error: close late-signal ack hook: $!\n";
}
if (syscall($SYS_RENAMEAT2, fileno($parent), $log_tmp_leaf,
        fileno($parent), $option{'log-leaf'}, $RENAME_NOREPLACE) != 0) {
    my $error = "$!";
    my $collision = $! == EEXIST;
    unlink($log_tmp_ref) or die "bounded-log-error: cleanup log temporary: $!\n";
    $log_tmp_created = 0;
    die($collision ? "bounded-log-error: log output collision\n" :
        "bounded-log-error: publish log: $error\n");
}
$log_published = 1;
$parent->sync or die "bounded-log-error: fsync log parent: $!\n";

my $receipt_text = join('',
    "schema=simple-bounded-process-log-v1\n", "status=complete\n",
    "reason=$reason\n", "raw_status=$raw_status\n",
    "max_bytes=$option{'max-bytes'}\n", "bytes_captured=$bytes_captured\n",
    "timeout_seconds=$option{'timeout-seconds'}\n",
    "term_grace_seconds=$option{'term-grace-seconds'}\n",
    "combined_stream=stdout-stderr\n", "process_group=setsid\n",
    "artifact_limit=none\n", "log_leaf=$option{'log-leaf'}\n",
    "log_sha256=$log_sha256\n");
sysopen(my $receipt, $receipt_tmp_ref,
    O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW, 0600) or
    die "bounded-log-error: create receipt temporary: $!\n";
$receipt_tmp_created = 1;
write_all($receipt, $receipt_text);
$receipt->sync or die "bounded-log-error: fsync receipt: $!\n";
close($receipt) or die "bounded-log-error: close receipt: $!\n";
if (syscall($SYS_RENAMEAT2, fileno($parent), $receipt_tmp_leaf,
        fileno($parent), $option{'receipt-leaf'}, $RENAME_NOREPLACE) != 0) {
    my $error = "$!";
    my $collision = $! == EEXIST;
    unlink($receipt_tmp_ref) or die "bounded-log-error: cleanup receipt temporary: $!\n";
    $receipt_tmp_created = 0;
    die($collision ? "bounded-log-error: receipt output collision; log retained without authoritative receipt\n" :
        "bounded-log-error: publish receipt: $error\n");
}
$receipt_published = 1;
$parent->sync or die "bounded-log-error: fsync receipt parent: $!\n";
close($parent) or die "bounded-log-error: close parent: $!\n";

if ($cancel_before_commit) {
    my $number = $signal_number{$caught};
    $SIG{$caught} = 'DEFAULT';
    kill($number, $$);
    defined(sigprocmask(SIG_SETMASK, $old_set)) or POSIX::_exit($raw_status);
    POSIX::_exit($raw_status);
}
print STDERR "bounded-log-error: $reason\n" if $reason ne 'child-exit' && $reason ne 'child-signal';
exit($raw_status);
