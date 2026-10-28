#!/usr/bin/env python3
"""Qualify actual source routes with an explicit native runner and child."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument("--runner", required=True, type=Path)
parser.add_argument("--child", required=True, type=Path)
parser.add_argument("--out", required=True, type=Path)
args = parser.parse_args()
repo = Path(__file__).resolve().parents[3]
runner, child, out = args.runner.resolve(), args.child.resolve(), args.out.resolve()
for executable in (runner, child):
    if not executable.is_file() or not os.access(executable, os.X_OK):
        parser.error(f"not an executable: {executable}")
out.mkdir(parents=True, exist_ok=False)
(out / "tmp").mkdir()
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
identity = [f"runner_sha256: {digest(runner)}", f"child_sha256: {digest(child)}",
            "source_head: " + subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()]
(out / "identity.sdn").write_text("\n".join(identity) + "\n")
env = os.environ.copy()
for key in list(env):
    if key.startswith(("SIMPLE_BOOTSTRAP_SESSION", "SIMPLE_NATIVE_BUILD", "SIMPLE_MANAGED_")):
        env.pop(key)
env.update(SIMPLE_BINARY=str(child), SIMPLE_TEST_BINARY=str(child), SIMPLE_LIB=str(repo / "src"),
           SIMPLE_PROJECT_ROOT=str(repo), TMPDIR=str(out / "tmp"), SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB="4194304")
failures = 0
rows = []
fixtures = sorted((repo / "test/fixtures/test_runner_source_routes/calibration").iterdir())
for index, path in enumerate(fixtures):
    expected = 0 if "green" in path.name else 1
    argv = [str(runner), str(path), "--mode=interpreter", "--no-cache", "--no-db", "--no-cover-check", "--no-self-protect", "--no-fork", "--timeout=12"]
    if path.name.startswith(("comment_", "slashcomment_", "doublecomment_", "docstring_", "mixed_")):
        argv.append("--spl-doctest")
    env["SIMPLE_PROCESS_TREE_RSS_RECEIPT"] = str(out / (path.name + ".rss.env"))
    command = ["sh", str(repo / "scripts/bootstrap/run-process-group-timeout.shs"), "30", "2"] + argv
    start = time.monotonic()
    with (out / (path.name + ".stdout")).open("w") as stdout, (out / (path.name + ".stderr")).open("w") as stderr:
        actual = subprocess.run(command, cwd=repo, env=env, stdout=stdout, stderr=stderr).returncode
    shown = (out / (path.name + ".stdout")).read_text() + (out / (path.name + ".stderr")).read_text()
    valid = actual == expected and "Resource limit exceeded ()" not in shown
    if path.name in ("plain_early_exit_test.spl", "plain_spoof_test.spl"):
        valid = valid and ("structured BDD evidence unavailable" in shown or "no BDD examples executed" in shown)
    if path.name == "plain_green_test.spl":
        valid = valid and "Results: 1 total, 1 passed, 0 failed" in shown
    if path.name.startswith("mixed_") and path.name != "mixed_empty_spec.spl":
        valid = valid and "Results:" in shown and "SPL Doctest:" in shown
    if "red" in path.name:
        valid = valid and ("CALIBRATION_EXPECTED_" in shown or "expected 41 to equal 42" in shown)
    if not valid:
        failures += 1
    status = "PASS" if valid else "FAIL"
    seconds = round(time.monotonic() - start, 3)
    rows.extend([f"case_{index}_input: {path.name}", f"case_{index}_sha256: {digest(path)}", f"case_{index}_expected: {expected}", f"case_{index}_actual: {actual}", f"case_{index}_seconds: {seconds}", f"case_{index}_status: {status}"])
    (out / "rows.sdn").write_text("\n".join(rows) + "\n")
    print(f"{status} {path.name} expected={expected} actual={actual}", flush=True)
print(f"SOURCE_ROUTE_ACCEPTANCE cases={len(fixtures)} failures={failures}")
raise SystemExit(1 if failures else 0)
