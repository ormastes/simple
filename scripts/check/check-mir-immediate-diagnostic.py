#!/usr/bin/env python3
"""Check the real native reporting fixture before killing later work.

This does not compile a compiler or claim the full phase-3 loop passed.
The output directory must be new; stdout, stderr and an SDN result are kept.
"""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--executable", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--scope", required=True, choices=("full-owner", "presentation-only"))
    args = parser.parse_args()
    executable = args.executable.resolve(strict=True)
    args.output.mkdir(parents=True, exist_ok=False)
    stdout_path = args.output / "stdout.log"
    env = dict(os.environ, SIMPLE_COMPILER_PHASE_PROFILE="0", SIMPLE_COMPILER_TRACE="0")
    observed = False
    was_running = False
    with stdout_path.open("wb") as stdout, (args.output / "stderr.log").open("wb") as stderr:
        child = subprocess.Popen([str(executable)], stdout=stdout, stderr=stderr, env=env)
        try:
            deadline = time.monotonic() + 10
            while child.poll() is None and time.monotonic() < deadline:
                if b"[mir-module-failure]" in stdout_path.read_bytes():
                    observed = True
                    was_running = child.poll() is None
                    break
                time.sleep(0.05)
        finally:
            if child.poll() is None:
                child.kill()  # No normal-exit stdio flushing can rescue the test.
            child.wait(timeout=5)
    output = stdout_path.read_bytes()
    passed = (observed and was_running and child.returncode != 0
              and output.count(b"[mir-module-failure]") == 1
              and b"fatal_count=2" in output
              and b"undefined variable: retained-before-later-module" in output
              and b"older fatal" not in output and len(output) < 1500)
    status = "PASS" if passed else "FAIL"
    digest = hashlib.sha256(executable.read_bytes()).hexdigest()
    (args.output / "result.sdn").write_text(
        'schema: "mir-immediate-diagnostic-test/1"\n'
        f'status: {status}\nexecutable_sha256: "{digest}"\n'
        f'scope: "{args.scope}"\n'
        f'observed_before_kill: {str(observed).lower()}\n'
        f'process_was_running: {str(was_running).lower()}\n'
        f'exit_code: {child.returncode}\n'
        'profiling: false\nfull_phase3_admission: false\n', encoding="utf-8")
    print(f"{status}: {args.output / 'result.sdn'}")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
