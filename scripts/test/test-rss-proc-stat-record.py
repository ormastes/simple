#!/usr/bin/env python3
"""Test the watchdog's real bounded reader and existing Linux field parser."""
import ctypes
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
source = (root / "scripts/resource/process-tree-rss-watchdog.pl").read_text()
reader = source[source.index("sub read_proc_stat_record {"):source.index("sub snapshot {")]
start = source.index("            $line =~ /", source.index("sub snapshot {"))
parser = source[start:source.index("            $all{$pid}", start)]
program = "use strict; use warnings; use Errno qw(ESRCH ENOENT);\n" + reader + """
my ($path, $pid) = @ARGV;
open(my $fh, '<', $path) or die $!;
my $line = read_proc_stat_record($fh);
close($fh);
""" + parser + 'print "$2:$3:$4:$5:$6\\n";'


def inspect(path, pid):
    return subprocess.run(["perl", "-e", program, str(path), str(pid)],
                          capture_output=True, check=False)


if not Path("/proc/self/stat").exists():
    raise SystemExit("Linux /proc is required")
libc = ctypes.CDLL(None, use_errno=True)
original = ctypes.create_string_buffer(16)
assert libc.prctl(16, ctypes.byref(original), 0, 0, 0) == 0  # PR_GET_NAME
try:
    for name in (b"rss-normal", b"rss\n) tricky"):
        assert libc.prctl(15, ctypes.c_char_p(name), 0, 0, 0) == 0  # PR_SET_NAME
        path = Path(f"/proc/{os.getpid()}/stat")
        record = path.read_bytes()
        assert b"(" + name + b") " in record
        if b"\n" in name:
            assert b") " not in record.splitlines(keepends=True)[0], "baseline must truncate"
        result = inspect(path, os.getpid())
        assert result.returncode == 0, result.stderr.decode()
        parent, group, session, start_ticks, rss_pages = map(int, result.stdout.split(b":"))
        assert (parent, group, session) == (os.getppid(), os.getpgrp(), os.getsid(0))
        assert start_ticks > 0 and rss_pages >= 0
finally:
    assert libc.prctl(15, ctypes.byref(original), 0, 0, 0) == 0

with tempfile.TemporaryDirectory(prefix="rss-stat-record-") as temporary:
    path = Path(temporary) / "stat"
    for data, expected in ((b"123 (broken\n", b"malformed"),
                           (b"x" * 65537, b"oversized"),
                           (b"", b"malformed")):
        path.write_bytes(data)
        result = inspect(path, 123)
        assert result.returncode != 0 and expected in result.stderr, result.stderr

# Exercise the real reader deterministically at the post-open read boundary.
# A disappearing process is benign, but an unreadable live process is not.
race_program = "use strict; use warnings; use Errno qw(ESRCH ENOENT EACCES EIO);\n" + reader + r"""
package FailingStat;
sub TIEHANDLE { bless { errno => $_[1], partial => $_[2] }, $_[0] }
sub READ {
    if ($_[0]->{partial}) {
        $_[0]->{partial} = 0;
        $_[1] = '123 (partial';
        return length($_[1]);
    }
    $! = $_[0]->{errno};
    return undef;
}
package main;
for my $gone (ESRCH, ENOENT) {
    for my $partial (0, 1) {
        tie *STAT, 'FailingStat', $gone, $partial;
        my $record = read_proc_stat_record(\*STAT);
        die "vanished task retained a record" if defined($record);
        untie *STAT;
    }
}
for my $fatal (EACCES, EIO) {
    tie *STAT, 'FailingStat', $fatal, 0;
    my $ok = eval { read_proc_stat_record(\*STAT); 1 };
    die "unexpected read error was hidden" if $ok;
    die "unexpected diagnostic: $@" unless $@ =~ /cannot read \/proc stat record/;
    untie *STAT;
}
print "PASS: vanished process and fatal read errors\n";
"""
race = subprocess.run(["perl", "-e", race_program], capture_output=True, check=False)
assert race.returncode == 0, race.stderr.decode()
print("PASS: real normal/newline process names, field identities, malformed and oversized rejection; ESRCH/ENOENT before/after partial read; EACCES/EIO remain fatal")
