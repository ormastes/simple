#!/usr/bin/env python3
"""Check an already built native owner control executable (no compiler rebuild)."""
import argparse
import csv
import pathlib
import re
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=pathlib.Path)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parents[2]
    args.output.mkdir(parents=True, exist_ok=True)
    owner = "src/lib/nogc_sync_mut/test_runner/native_compile_contract.spl"
    sites = {}
    for number, line in enumerate((root / owner).read_text().splitlines(), 1):
        match = re.search(r"if runner_self_coverage_decision\(([1-6]),", line)
        if match:
            sites[int(match[1])] = number
    assert len(sites) == 6, "owner's declared probe catalog changed"
    for control, expected_exit in (("empty", 0), ("positive", 0), ("negative", 1)):
        result = subprocess.run([str(args.binary.resolve()), "--" + control],
                                cwd=root, text=True, capture_output=True, timeout=15)
        (args.output / (control + ".sdn")).write_text(result.stdout)
        (args.output / (control + ".stderr")).write_text(result.stderr)
        (args.output / (control + ".exit")).write_text(str(result.returncode) + "\n")
        assert result.returncode == expected_exit, (control, result.returncode, result.stderr)
        for marker in ("coverage_extension: decision-condition-v1",
                       "measurement: explicit-owner-decision-probes-v1",
                       "whole_runner_coverage: false", "automatic_source_coverage: false",
                       "declared_decisions: 6"):
            assert marker in result.stdout, (control, marker)
        rows = {}
        for line in result.stdout.splitlines():
            if not re.match(r"[1-6], ", line):
                continue
            row = next(csv.reader([line], skipinitialspace=True))
            site, path, source_line, column, yes, no = row
            assert path == owner
            assert int(source_line) == sites[int(site)], "stale authored probe location"
            assert int(column) == 4
            assert int(site) not in rows, "duplicate decision row"
            rows[int(site)] = (int(yes), int(no))
        assert set(rows) == set(sites), "zero-hit declarations must survive rendering"
        if control == "empty":
            assert all(pair == (0, 0) for pair in rows.values()), rows
        else:
            # All six production admission failures and the successful fallthrough
            # execute; each selected decision must observe both true and false.
            assert all(yes > 0 and no > 0 for yes, no in rows.values()), rows
            expected_failures = 1 if control == "negative" else 0
            assert f"assertion_failures={expected_failures}" in result.stdout
    print("PASS: six scoped owner decisions, zero-hit denominator, green/red controls")


if __name__ == "__main__":
    main()
