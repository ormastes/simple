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
program = "use strict; use warnings;\n" + reader + """
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
print("PASS: real normal/newline process names, field identities, malformed and oversized rejection")
