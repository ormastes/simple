#!/usr/bin/env python3
"""Exercise parity target linkage using the real checker and ClickEvent owner.

Run with --shell pointing to native Git Bash on Windows (not the WSL launcher).
This checks linkage and the existing LOC gates, not behavioral port completeness.
"""
import argparse
import csv
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shell", default="sh")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    tracked = set(subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", "HEAD", "src/app/llm_caret/claude_full"],
        cwd=root, text=True).splitlines())
    tables = {}
    names = {}
    for kind in ("file", "symbol"):
        name = f"llm_caret_claude_cli_full_parity_{kind}_matrix.tsv"
        names[kind] = name
        with (root / "doc/03_plan/trace" / name).open(newline="") as stream:
            reader = csv.DictReader(stream, delimiter="\t")
            rows = list(reader)
            tables[kind] = (reader.fieldnames, rows)
        for row in rows:
            target = row["target_simple_file"]
            if target not in tracked and target.replace("-", "_") in tracked:
                raise AssertionError(f"{kind}: stale target {target}")

    source = "ink/events/click-event.ts"
    owner = "src/app/llm_caret/claude_full/ink/events/click_event.spl"
    selected = {}
    for kind, (_, rows) in tables.items():
        selected[kind] = [dict(row) for row in rows if row["claude_file"] == source]
        assert selected[kind], f"missing {kind} coverage for {source}"
        assert all(row["target_simple_file"] == owner for row in selected[kind])
    assert any(row["symbol_kind"] == "class" for row in selected["symbol"])

    env = dict(os.environ)
    shell = shutil.which(args.shell) or args.shell
    env["PATH"] = str(Path(shell).resolve().parent) + os.pathsep + env.get("PATH", "")
    with tempfile.TemporaryDirectory(prefix="caret-parity-") as directory:
        fixture = Path(directory)
        trace = fixture / "doc/03_plan/trace"
        trace.mkdir(parents=True)
        destination = fixture / owner
        destination.parent.mkdir(parents=True)
        shutil.copyfile(root / owner, destination)
        checker = fixture / "check.sh"
        shutil.copyfile(root / "scripts/check/check-llm-caret-full-parity-implementation.shs", checker)

        def run(label, expected, marker, rows_by_kind):
            for kind, rows in rows_by_kind.items():
                with (trace / names[kind]).open("w", newline="") as stream:
                    writer = csv.DictWriter(stream, fieldnames=tables[kind][0], delimiter="\t", lineterminator="\n")
                    writer.writeheader()
                    writer.writerows(rows)
            result = subprocess.run([shell, "check.sh"], cwd=fixture, env=env,
                                    text=True, capture_output=True, timeout=30)
            assert result.returncode == expected, (label, result.returncode, result.stdout, result.stderr)
            assert marker in result.stdout, (label, result.stdout)
            print(f"PASS {label}")

        run("real-owner", 0, "STATUS: PASS", selected)
        historical = {kind: [dict(row, target_simple_file=owner.replace("click_event", "click-event"))
                             for row in rows] for kind, rows in selected.items()}
        run("historical-hyphen-target", 1, "class_target_files_missing=1", historical)
        destination.unlink()
        run("missing-owner", 1, "target_files_missing=1", selected)
        shutil.copyfile(root / owner, destination)
        short = {kind: [dict(row) for row in rows] for kind, rows in selected.items()}
        short["file"][0]["target_min_loc"] = str(len(destination.read_text().splitlines()) + 1)
        run("insufficient-LOC", 1, "target_loc_ge_required=0", short)
    print("STATUS: PASS parity target linkage (not full port parity)")


if __name__ == "__main__":
    main()
