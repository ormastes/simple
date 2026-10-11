#!/usr/bin/perl
# Real pipe/waitpid checks for receipt policy; no native owner or workload.
use strict;
use warnings;
use FindBin;
open(my $file, '<', "$FindBin::Bin/process-tree-rss-watchdog.pl") or die $!;
local $/;
my $source = <$file>;
close($file);
$source =~ s/^# Workload startup boundary.*\z//ms or die "guard startup marker missing";
@ARGV = ('--', 'true');
my $exercise = <<'EXERCISE';
my @cases = (
    ['verified cleanup and zero exit', 1, 0, 1, 0],
    ['EOF despite zero owner exit', 0, 0, 0, 0],
    ['EOF and failed owner exit', 0, 89, 0, 89 << 8],
    ['cleanup reply then failed owner exit', 1, 89, 0, 89 << 8],
    ['owner killed without cleanup reply', 0, -1, 0, 9],
);
for my $case (@cases) {
    my ($name, $reply, $exit, $expected, $raw) = @$case;
    pipe(my $input, $reaper_write) or die $!;
    pipe($reaper_read, my $output) or die $!;
    my $child = fork();
    defined($child) or die $!;
    if (!$child) {
        close($reaper_write); close($reaper_read);
        alarm 5;
        my $read = sysread($input, my $command, 1);
        POSIX::_exit(99) unless defined($read) && $read == 1 && $command eq 'Q';
        if ($reply) {
            my $line = "QUIET 1 0 $$ 123 0\n";
            my $sent = syswrite($output, $line);
            POSIX::_exit(99) unless defined($sent) && $sent == length($line);
        }
        if ($exit < 0) { kill 'KILL', $$; POSIX::_exit(99) }
        POSIX::_exit($exit);
    }
    close($input); close($output);
    ($leader, $reaper_identity, $reaper_buffer) = ($child, '123.0', '');
    ($reaper_retained, $reaper_owner_wait_status) = (0, -1);
    undef($child_status);
    my @warnings;
    my $quiet;
    { local $SIG{__WARN__} = sub { push @warnings, @_ }; $quiet = reaper_quiesce() }
    $quiet == $expected or die "$name: incorrect quiescence";
    $reaper_retained == !$expected or die "$name: unresolved reservation released";
    $reaper_owner_wait_status == $raw or die "$name: native wait status lost";
    !grep(/uninitialized/, @warnings) or die "$name: undefined numeric comparison";
    print "PASS $name\n";
}
pipe(my $closed_peer, $reaper_write) or die $!;
close($closed_peer);
my (@warnings, $error);
{
    local $SIG{__WARN__} = sub { push @warnings, @_ };
    eval { reaper_command('Q') };
    $error = $@;
}
close($reaper_write);
$error =~ /reaper command failed:/ && !@warnings or die "broken pipe diagnostic was not defined";
print "PASS broken pipe diagnostic\n";
for my $frame (
    "ERROR 1 123 sample nested-identity 124 0 3 0 -1 -1\n",
    "ERROR 1 123 stop sample-failed 1 0 0 0 1 9\n",
) {
    pipe($reaper_read, my $writer) or die $!;
    syswrite($writer, $frame) == length($frame) or die "diagnostic fixture write";
    close($writer);
    ($leader, $reaper_buffer) = (123, '');
    my $result = eval { reaper_line(time + 0.1) };
    !defined($result) && $@ eq "native reaper failure: $frame" or die "terminal diagnostic lost";
    close($reaper_read);
    print "PASS terminal diagnostic $frame";
}
EXERCISE
eval "$source\n$exercise";
die $@ if $@;
