"""Run an already-compiled scope fixture in a private, initially empty checkout.

This runner does not build a compiler or grant producer admission. The caller
must retain its build/producer/runtime receipt separately. All evidence is kept.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("binary", type=Path)
    parser.add_argument("--expected-sha256", required=True)
    parser.add_argument("--evidence-parent", type=Path, required=True)
    args = parser.parse_args()
    binary = args.binary.resolve(strict=True)
    with binary.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    if digest != args.expected_sha256:
        parser.error("compiled fixture digest mismatch")
    args.evidence_parent.mkdir(parents=True, exist_ok=True)
    root = Path(tempfile.mkdtemp(prefix="parent-closure-native-", dir=args.evidence_parent)).resolve()
    env = os.environ.copy()
    # A fixture establishes its own real source authority. Never inherit a
    # live bootstrap snapshot/epoch, child shard role, or warm candidate sink.
    for key in list(env):
        if key.startswith(("SIMPLE_SCV_", "SIMPLE_PARSE_CLOSURE_")) or key in {
            "SIMPLE_PARSE_SHARD", "SIMPLE_HIR_SHARD", "SIMPLE_NATIVE_BUILD_WARM_CLOSURE_CANDIDATE",
        }:
            del env[key]
    env["SIMPLE_PARENT_CLOSURE_FIXTURE_ROOT"] = root.as_posix()
    with (root / "stdout.log").open("wb") as out, (root / "stderr.log").open("wb") as err:
        result = subprocess.run([str(binary), binary.as_posix()], cwd=root, env=env,
                                stdout=out, stderr=err, check=False)
    output = (root / "stdout.log").read_text(encoding="utf-8", errors="replace")
    rows = [line for line in output.splitlines() if line.startswith("parent-closure checks=")]
    # The executable's actual dynamic count is authoritative; no empty or
    # truncated output may turn a raw zero exit into a successful result.
    import re
    match = re.fullmatch(r"parent-closure checks=(\d+) failures=(\d+)", rows[0]) if len(rows) == 1 else None
    passed = result.returncode == 0 and match is not None and int(match[1]) > 0 and int(match[2]) == 0
    report = {"fixture_sha256": digest, "exit_code": result.returncode,
              "checks": int(match[1]) if match else None,
              "failures": int(match[2]) if match else None, "passed": passed,
              "formal_admission": False, "evidence_root": str(root)}
    (root / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
