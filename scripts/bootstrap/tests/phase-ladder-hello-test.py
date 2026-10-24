#!/usr/bin/env python3
"""Exercise the real POSIX ladder gate with shell fixtures, not compilers.

These tests establish runner control flow only; they cannot qualify a compiler.
Run on a POSIX host: python3 scripts/bootstrap/tests/phase-ladder-hello-test.py --jobs 24
"""
import argparse
import concurrent.futures
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


CASES = [
    ("lf", b"phase-ladder-2-ok\n", 0, b"", True),
    ("crlf", b"phase-ladder-2-ok\r\n", 0, b"", True),
    ("marker-exit17", b"phase-ladder-2-ok\n", 17, b"native failure\n", False),
    ("marker-exit1", b"phase-ladder-2-ok\r\n", 1, b"native failure\n", False),
    ("extra-line", b"phase-ladder-2-ok\nextra\n", 0, b"", False),
    ("prefix", b"prefix-phase-ladder-2-ok\n", 0, b"", False),
    ("suffix", b"phase-ladder-2-ok-suffix\n", 0, b"", False),
    ("wrong-phase", b"phase-ladder-3-ok\n", 0, b"", False),
    ("missing", b"", 0, b"", False),
    ("missing-newline", b"phase-ladder-2-ok", 0, b"", False),
    ("extra-blank-line", b"phase-ladder-2-ok\n\n", 0, b"", False),
    ("missing-exit17", b"", 17, b"native failure\n", False),
]


def script(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")
    path.chmod(0o755)


def check_case(base, production, shell, platform, case):
    name, stdout, raw_exit, stderr, accepted = case
    root = base / (platform + "-" + name)
    root.mkdir()
    exe = ".exe" if platform.startswith("windows-") else ""
    scripts = root / "scripts/bootstrap"
    scripts.mkdir(parents=True)
    shutil.copyfile(production, scripts / "phase-ladder-step.shs")
    script(scripts / "build-next-phase-ci.shs", """#!/bin/sh
set -eu
case $1 in windows-*) exe=.exe ;; *) exe= ;; esac
mkdir -p build/bootstrap/stage2
cp "$FIXTURE_ROOT/compiler" "build/bootstrap/stage2/simple$exe"
chmod +x "build/bootstrap/stage2/simple$exe"
""")
    script(root / "compiler", """#!/bin/sh
set -eu
if [ "$1" = --version ]; then
  echo 'shell fixture: not compiler qualification'
  exit 0
fi
[ "$1" = native-build ] && [ "$3" = -o ]
cp "$FIXTURE_ROOT/hello-program" "$4"
chmod +x "$4"
""")
    script(root / "hello-program", """#!/bin/sh
cat "$FIXTURE_ROOT/native.stdout"
cat "$FIXTURE_ROOT/native.stderr" >&2
exit "$FIXTURE_EXIT"
""")
    (root / "native.stdout").write_bytes(stdout)
    (root / "native.stderr").write_bytes(stderr)
    handoff = root / "in" / (platform + "-p1")
    handoff.mkdir(parents=True)
    (handoff / "PHASE").write_text("1\n")
    script(handoff / ("simple" + exe), "#!/bin/sh\nexit 99\n")
    env = os.environ.copy()
    env.update(FIXTURE_ROOT=str(root), FIXTURE_EXIT=str(raw_exit),
               PHASE_LADDER_SELFHOST_THREADS="24", PHASE_LADDER_ESSENTIALS_FROM="3",
               GITHUB_OUTPUT=str(root / "github-output"))
    result = subprocess.run([shell, "scripts/bootstrap/phase-ladder-step.shs",
                             platform, "in", "out", "24"], cwd=root, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
    (root / "runner.stdout").write_bytes(result.stdout)
    (root / "runner.stderr").write_bytes(result.stderr)
    evidence = root / "build/ladder/evidence/hello"
    assert (evidence / "exit-status").read_text() == str(raw_exit) + "\n", name
    assert (evidence / "stdout").read_bytes() == stdout, name
    assert (evidence / "stderr").read_bytes() == stderr, name
    assert (evidence / "hello.spl").is_file(), name
    assert (evidence / ("hello" + exe)).is_file(), name
    phase = root / "out" / (platform + "-p2") / "PHASE"
    rejected = root / "out" / (platform + "-rejected-p2") / ("simple" + exe)
    assert (result.returncode == 0) == accepted, (name, result.returncode, result.stderr)
    assert phase.exists() == accepted, name
    if accepted:
        assert phase.read_text() == "2\n", name
    else:
        assert rejected.read_bytes() == (root / "compiler").read_bytes(), name
        assert not list((root / "out").glob("*/PHASE")), name
        assert "phase=" not in (root / "github-output").read_text() if (root / "github-output").exists() else True
    return platform + ":" + name


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=24)
    parser.add_argument("--shell", default="sh")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    production = Path(__file__).resolve().parents[1] / "phase-ladder-step.shs"
    base = Path(tempfile.mkdtemp(prefix="phase-ladder-hello-"))
    print("evidence=" + str(base), flush=True)
    work = [(platform, case) for platform in ("linux-x86_64", "windows-x86_64") for case in CASES]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(check_case, base, production, args.shell, platform, case)
                   for platform, case in work]
        for future in futures:
            print("PASS " + future.result())
    print("PASS: 24 shell controls; no real compiler qualification")


if __name__ == "__main__":
    main()
