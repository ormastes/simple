#!/usr/bin/perl
# Parser/IPC negatives; no native helper or workload is launched.
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
{
    no warnings 'redefine';
    *verify_session_helper = sub { };
    *reaper_command = sub { };
}
$leader = $session_id = 123;
my $valid = "SAMPLE 1 123 124 -1 2\n123 1 123 123 42 0 1 0\n124 123 124 124 100 0 2 0\nEND\n";
my @cases = (
    ['valid owned new SID', $valid, 1],
    ['truncated frame', "SAMPLE 1 123 124 -1 2\n", 0],
    ['oversized count', "SAMPLE 1 123 124 -1 16386\n", 0],
    ['wrong owner', $valid =~ s/SAMPLE 1 123/SAMPLE 1 999/r, 0],
    ['invalid status', $valid =~ s/124 -1/124 999999/r, 0],
    ['malformed row', $valid =~ s/ 100 / nope /r, 0],
    ['duplicate PID', $valid =~ s/\n124 123/\n123 123/r, 0],
    ['owner SID changed', $valid =~ s/123 1 123 123/123 1 123 456/r, 0],
    ['invalid microseconds', $valid =~ s/ 2 0\n/ 2 1000000\n/r, 0],
    ['missing END', $valid =~ s/END\n//r, 0],
);
for my $case (@cases) {
    my ($name, $frame, $expected) = @$case;
    pipe($reaper_read, my $writer) or die $!;
    syswrite($writer, $frame) == length($frame) or die "fixture pipe write";
    close($writer);
    ($reaper_buffer, $reaper_identity, $reaper_payload) = ('', '', 0);
    undef($child_status);
    $sample_started_at = time;
    my $result = eval { reaper_snapshot() };
    (!!$result) == $expected or die "$name: expected acceptance=$expected, error=$@";
    if ($expected) {
        $result->{124}{rss} == 100 && $result->{124}{session} == 124 &&
            $reaper_cross_session == 1 or die "owned cross-session metadata lost";
    }
    close($reaper_read);
    print "PASS $name\n";
}
pipe($reaper_read, my $silent_writer) or die $!;
$reaper_buffer = '';
my $begin = time;
my $line = eval { reaper_line(time + 0.03) };
!defined($line) && $@ && time - $begin < 0.5 or die "silent peer read was not bounded";
close($silent_writer); close($reaper_read);
print "PASS silent peer deadline\n";
EXERCISE
eval "$source\n$exercise";
die $@ if $@;
