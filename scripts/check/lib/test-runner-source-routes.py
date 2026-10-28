#!/usr/bin/env python3
"""Qualify actual source routes with an explicit native runner and child."""
import argparse
import hashlib
import json
import re
import os
from pathlib import Path
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument("--runner", required=True, type=Path)
parser.add_argument("--child", required=True, type=Path)
parser.add_argument("--out", required=True, type=Path)
parser.add_argument("--verify-existing", action="store_true", help="verify pinned existing receipts; collect missing full diagnostic evidence only")
args = parser.parse_args()
repo = Path(__file__).resolve().parents[3]
runner, child, out = args.runner.resolve(), args.child.resolve(), args.out.resolve()
for executable in (runner, child):
    if not executable.is_file() or not os.access(executable, os.X_OK):
        parser.error(f"not an executable: {executable}")
if not args.verify_existing:
    out.mkdir(parents=True, exist_ok=False)
    (out / "tmp").mkdir()
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
identity = [f"runner_sha256: {digest(runner)}", f"child_sha256: {digest(child)}",
            "source_head: " + subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()]
prior = {}
if args.verify_existing:
    identities = dict(line.split(": ", 1) for line in (out / "identity.sdn").read_text().splitlines())
    if identities["runner_sha256"] != digest(runner) or identities["child_sha256"] != digest(child):
        parser.error("existing receipt executable identities changed")
    prior = dict(line.split(": ", 1) for line in (out / "rows.sdn").read_text().splitlines())
else:
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
    if args.verify_existing:
        if prior[f"case_{index}_input"] != path.name or prior[f"case_{index}_sha256"] != digest(path):
            parser.error(f"existing fixture identity changed: {path.name}")
        actual = int(prior[f"case_{index}_actual"])
    else:
        with (out / (path.name + ".stdout")).open("w") as stdout, (out / (path.name + ".stderr")).open("w") as stderr:
            actual = subprocess.run(command, cwd=repo, env=env, stdout=stdout, stderr=stderr).returncode
    shown = (out / (path.name + ".stdout")).read_text() + (out / (path.name + ".stderr")).read_text()
    valid = actual == expected and "Resource limit exceeded ()" not in shown
    if path.name in ("plain_early_exit_test.spl", "plain_spoof_test.spl"):
        valid = valid and ("structured BDD evidence unavailable" in shown or "no BDD examples executed" in shown)
    if path.name == "plain_green_test.spl":
        valid = valid and "Results: 1 total, 1 passed, 0 failed" in shown
    if path.name == "plain_bdd_prefix_names_green_test.spl":
        valid = valid and "Results: 1 total, 1 passed, 0 failed" in shown and "CALIBRATION_EXPECTED_plain_bdd_prefix_names_test" not in shown
    if path.name.startswith("mixed_") and path.name != "mixed_empty_spec.spl":
        valid = valid and "Results:" in shown and "SPL Doctest:" in shown
    if "red" in path.name:
        assertion_seen = "CALIBRATION_EXPECTED_" in shown or "expected 41 to equal 42" in shown
        if not assertion_seen and "--spl-doctest" in argv and actual == 1:
            # The console formatter may show engine-demotion before the panic.
            # Capture the native worker's complete typed BlockResult stderr;
            # source-code fields containing the panic string never count.
            diagnostic = out / (path.name + ".diagnostic.sdn")
            diagnostic_env = env.copy()
            diagnostic_env["SIMPLE_TEST_SDN_WORKER_AUTH"] = "1"
            diagnostic_env["SIMPLE_PROCESS_TREE_RSS_RECEIPT"] = str(out / (path.name + ".diagnostic.rss.env"))
            diagnostic_argv = [str(runner), "--test-sdn-worker", "--test-sdn-result=" + str(diagnostic)] + argv[1:]
            diagnostic_command = ["sh", str(repo / "scripts/bootstrap/run-process-group-timeout.shs"), "30", "2"] + diagnostic_argv
            diagnostic_status = None
            if not (args.verify_existing and diagnostic.is_file()):
                with (out / (path.name + ".diagnostic.stdout")).open("w") as stdout, (out / (path.name + ".diagnostic.stderr")).open("w") as stderr:
                    diagnostic_status = subprocess.run(diagnostic_command, cwd=repo, env=diagnostic_env, stdout=stdout, stderr=stderr).returncode
                (out / (path.name + ".diagnostic.exit")).write_text(str(diagnostic_status) + "\n")
            if diagnostic.is_file() and diagnostic_status in (None, 1):
                for field in re.finditer(r'\bstderr: ("(?:\\.|[^"\\])*")', diagnostic.read_text()):
                    captured = json.loads(field[1])
                    if "error: semantic: panic: CALIBRATION_EXPECTED_" in captured:
                        assertion_seen = True
            if not assertion_seen and path.name == "mixed_doc_red_spec.spl":
                # Mixed native SDN serialization can fail independently after
                # correct text results. Preserve that failure and diagnose the
                # EXACT same-file doctest composite with the pinned child.
                # The original native runner must still report spec PASS and
                # doctest FAIL; this diagnostic never supplies its verdict.
                bdd = (path.parent / "spec_green_spec.spl").read_text()
                doc = (path.parent / "comment_red.spl").read_text()
                if path.read_text() == bdd + "\n" + doc:
                    lines = doc.splitlines()
                    if lines[0] == "# ```simple" and lines[-1] == "# ```":
                        code = "\n".join(line[2:] for line in lines[1:-1])
                        line_number = path.read_text().splitlines().index("# ```simple") + 1
                        composite = path.read_text() + f"\n\n# --- doctest from line {line_number} ---\nuse std.spec.*\n" + code
                        receipt_source = out / (path.name + ".composite.spl")
                        receipt_source.write_text(composite)
                        directory = repo / ".simple/doctest"
                        directory.mkdir(parents=True, exist_ok=True)
                        temporary = directory / f"acceptance_composite_{os.getpid()}.spl"
                        with temporary.open("x") as stream:
                            stream.write(composite)
                        composite_env = env.copy()
                        composite_env["SIMPLE_PROCESS_TREE_RSS_RECEIPT"] = str(out / (path.name + ".composite.rss.env"))
                        composite_command = ["sh", str(repo / "scripts/bootstrap/run-process-group-timeout.shs"), "30", "2", str(child), str(temporary)]
                        try:
                            with (out / (path.name + ".composite.stdout")).open("w") as stdout, (out / (path.name + ".composite.stderr")).open("w") as stderr:
                                composite_status = subprocess.run(composite_command, cwd=repo, env=composite_env, stdout=stdout, stderr=stderr).returncode
                        finally:
                            temporary.unlink()
                        (out / (path.name + ".composite.exit")).write_text(str(composite_status) + "\n")
                        complete_error = (out / (path.name + ".composite.stderr")).read_text()
                        assertion_seen = composite_status == 1 and "error: semantic: panic: CALIBRATION_EXPECTED_comment_red" in complete_error and "Results: 1 total, 1 passed, 0 failed" in shown and "SPL Doctest: 0 passed, 1 failed" in shown
        valid = valid and assertion_seen
    if not valid:
        failures += 1
    status = "PASS" if valid else "FAIL"
    seconds = round(time.monotonic() - start, 3)
    rows.extend([f"case_{index}_input: {path.name}", f"case_{index}_sha256: {digest(path)}", f"case_{index}_expected: {expected}", f"case_{index}_actual: {actual}", f"case_{index}_seconds: {seconds}", f"case_{index}_status: {status}"])
    (out / ("rows.verified.sdn" if args.verify_existing else "rows.sdn")).write_text("\n".join(rows) + "\n")
    print(f"{status} {path.name} expected={expected} actual={actual}", flush=True)
print(f"SOURCE_ROUTE_ACCEPTANCE cases={len(fixtures)} failures={failures}")
raise SystemExit(1 if failures else 0)
