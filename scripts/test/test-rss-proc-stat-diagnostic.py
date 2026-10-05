#!/usr/bin/env python3
"""Malformed proc records remain fatal and produce bounded byte evidence."""
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[2]
source = (root / "scripts/resource/process-tree-rss-watchdog.pl").read_text()
start = source.index("            $line =~ /", source.index("sub snapshot {"))
parser = source[start:source.index("            $all{$pid}", start)]
program = "use strict; use warnings; my $pid = 123; local $/; my $line = <STDIN>;\n" + parser

for record in (b"123 (partial", b"123 (comm\nmore) R 1 2 3 short\n", b"x" * 4096):
    result = subprocess.run(["perl", "-e", program], input=record,
                            capture_output=True, check=False)
    assert result.returncode != 0, "malformed record was accepted"
    diagnostic = result.stderr.decode("ascii")
    evidence = re.search(r"malformed /proc/123/stat \(bytes=(\d+) prefix_hex=([0-9a-f]*)\)", diagnostic)
    assert evidence, f"missing bounded malformed-record evidence: {diagnostic!r}"
    assert int(evidence[1]) == len(record), diagnostic
    assert evidence[2] == record[:256].hex(), diagnostic
    assert len(evidence[2]) <= 512 and len(result.stderr) < 700, "diagnostic was unbounded"
    assert result.stdout == b"", result.stdout

print("PASS: malformed records remain fatal; exact length and at most 256 bytes of hex evidence")
