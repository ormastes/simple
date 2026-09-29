#!/usr/bin/env python3
"""Exercise real Phase3 matrix rejection gates; no admitted compiler is fabricated.

The inert host executable is only a startup fixture. Positive Phase3 execution
requires a real canonical manifest and remains a separate bootstrap criterion.
"""
import argparse
from contextlib import nullcontext
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--shell", default="bash")
    parser.add_argument("--fixture-executable", type=Path, default=Path("/bin/true"))
    args = parser.parse_args()
    root = args.source_root.resolve()
    args.work_root.mkdir(parents=True, exist_ok=True)
    compiler = args.fixture_executable.resolve(strict=True)
    digest = hashlib.sha256(compiler.read_bytes()).hexdigest()
    script = root / "scripts/bootstrap/bootstrap-phase-verification.shs"
    # Retain every diagnostic, including a failed fixture, under the chosen root.
    with nullcontext(tempfile.mkdtemp(prefix="phase3-binding-", dir=args.work_root)) as temp:
        base = Path(temp)
        invalid = base / "invalid-provenance.env"
        invalid.write_text("schema=not-stage3-admission\n", encoding="utf-8")
        linked = base / "linked-provenance.env"
        try:
            linked.symlink_to(invalid)
        except OSError as error:
            raise RuntimeError("This rejection harness requires file-symlink creation; use WSL or enable the native host capability. No gate was skipped.") from error
        cases = [
            ("missing-provenance", ["--phase=stage3"], "Stage3 requires admitted provenance"),
            ("wrong-phase", ["--phase=stage2", f"--stage3-provenance={invalid}"], "stage3-only"),
            ("temporary-hash", ["--phase=stage3", f"--stage3-provenance={invalid}", "--hash-policy=temporary"], "canonical provenance"),
            ("missing-file", ["--phase=stage3", f"--stage3-provenance={base / 'missing.env'}"], "invalid Stage3 provenance file"),
            ("symlink-file", ["--phase=stage3", f"--stage3-provenance={linked}"], "invalid Stage3 provenance file"),
            ("invalid-authority", ["--phase=stage3", f"--stage3-provenance={invalid}"], "Stage3 provenance is not current"),
        ]
        for name, options, diagnostic in cases:
            work = base / name
            command = [args.shell, str(script), f"--compiler={compiler}",
                       f"--compiler-sha256={digest}", f"--source-root={root}",
                       f"--work-root={work}", *options]
            env = dict(os.environ, TMPDIR=str(base), SIMPLE_NO_BOOTSTRAP_DELEGATE="1",
                       SIMPLE_NO_STUB_FALLBACK="1", BOOTSTRAP_STAGE2_TEST_DELEGATE="0")
            result = subprocess.run(command, cwd=root, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=90)
            (base / f"{name}.log").write_text(result.stdout, encoding="utf-8")
            if result.returncode != 2 or diagnostic not in result.stdout:
                raise AssertionError(f"{name}: unexpected exit/diagnostic: {result.returncode}\n{result.stdout}")
            if list(work.glob("outputs/**/command-owners.*.env")):
                raise AssertionError(f"{name}: rejected authority published command owners")
            print(f"PASS {name}: rejected before command-owner publication")
    print("PASS 6 rejection gates; positive admitted Phase3 execution remains pending")


if __name__ == "__main__":
    main()
