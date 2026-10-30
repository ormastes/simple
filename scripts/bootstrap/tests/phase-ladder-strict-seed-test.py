#!/usr/bin/env python3
"""Exercise the actual phase-ladder seed command with controlled shell tools.

These fixtures verify runner environment forwarding and failure/handoff control
flow only. The failing seed fixture models a strict unresolved-return link
failure; it does not exercise actual alias resolution. The passing fixture does
not compile Simple or qualify a compiler.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


REPO = Path(__file__).resolve().parents[3]
PLATFORM = "linux-x86_64"


def write_script(path, body):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8", newline="\n")
    path.chmod(0o755)


def fixture(root, production, ambient, fail_seed):
    root.mkdir(parents=True)
    scripts = root / "scripts/bootstrap"
    scripts.mkdir(parents=True)
    shutil.copyfile(production, scripts / "phase-ladder-step.shs")
    shutil.copyfile(REPO / "scripts/bootstrap/build-next-phase-ci.shs",
                    scripts / "build-next-phase-ci.shs")
    write_script(scripts / "resolve-bootstrap-compiler.shs", """#!/bin/sh
echo 'controlled resolver: no candidate' >&2
exit 1
""")

    fakebin = root / "fakebin"
    fakebin.mkdir()
    write_script(fakebin / "cargo", """#!/bin/sh
set -eu
count=0
[ ! -f "$FIXTURE_ROOT/cargo-count" ] || count=$(cat "$FIXTURE_ROOT/cargo-count")
count=$((count + 1))
echo "$count" > "$FIXTURE_ROOT/cargo-count"
printf '%s\n' "$*" >> "$FIXTURE_ROOT/cargo-calls"
if [ "$count" -eq 2 ]; then
  mkdir -p target/bootstrap
  cp "$FIXTURE_ROOT/seed-compiler" target/bootstrap/simple
  chmod +x target/bootstrap/simple
fi
""")

    write_script(root / "seed-compiler", """#!/bin/sh
set -eu
if [ "$1" = --version ]; then
  echo 'fixture compiler: not qualification'
  exit 0
fi
[ "$1" = native-build ]
if [ "${2:-}" = --source ]; then
  printf 'SIMPLE_NO_STUB_FALLBACK=%s\nSIMPLE_BOOTSTRAP=%s\n' \\
    "${SIMPLE_NO_STUB_FALLBACK-unset}" "${SIMPLE_BOOTSTRAP-unset}" > "$FIXTURE_ROOT/seed-env"
  if [ "$FIXTURE_SEED_FAIL" = 1 ]; then
    echo 'strict-only unresolved return: fixture failure' >&2
    exit 73
  fi
  output=
  while [ "$#" -gt 0 ]; do
    if [ "$1" = --output ]; then output=$2; shift 2; else shift; fi
  done
  [ -n "$output" ]
  cp "$FIXTURE_ROOT/phase-one-compiler" "$output"
  chmod +x "$output"
else
  [ "$2" = "$FIXTURE_ROOT/hello-input.spl" ] || [ "${2##*/}" = hello.spl ]
  [ "$3" = -o ]
  cp "$FIXTURE_ROOT/hello-program" "$4"
  chmod +x "$4"
fi
""")
    write_script(root / "phase-one-compiler", """#!/bin/sh
set -eu
if [ "$1" = --version ]; then
  echo 'fixture compiler: not qualification'
  exit 0
fi
[ "$1" = native-build ]
[ "${2##*/}" = hello.spl ]
[ "$3" = -o ]
cp "$FIXTURE_ROOT/hello-program" "$4"
chmod +x "$4"
""")
    write_script(root / "hello-program", """#!/bin/sh
printf 'phase-ladder-1-ok\\n'
""")

    (root / "config").mkdir()
    (root / "config/bootstrap.sdn").write_text("schema: fixture\n", encoding="utf-8")
    (root / "src/compiler_rust").mkdir(parents=True)
    (root / "src/compositions/kernel_llvm_cranelift").mkdir(parents=True)
    (root / "src").joinpath("app/cli").mkdir(parents=True)
    (root / "src/app/cli/bootstrap_main.spl").write_text("fn main(): pass\n", encoding="utf-8")
    (root / "in").mkdir()
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    subprocess.run(["git", "config", "user.email", "fixture@example.invalid"], cwd=root, check=True)
    subprocess.run(["git", "config", "user.name", "Fixture"], cwd=root, check=True)
    subprocess.run(["git", "add", "config/bootstrap.sdn"], cwd=root, check=True)
    subprocess.run(["git", "commit", "-qm", "fixture"], cwd=root, check=True)

    env = os.environ.copy()
    env.update(PATH=str(fakebin) + os.pathsep + env["PATH"],
               FIXTURE_ROOT=str(root), FIXTURE_SEED_FAIL="1" if fail_seed else "0",
               PHASE_LADDER_SEED_FILE_TIMEOUT="3", GITHUB_OUTPUT=str(root / "github-output"))
    if ambient is None:
        env.pop("SIMPLE_NO_STUB_FALLBACK", None)
    else:
        env["SIMPLE_NO_STUB_FALLBACK"] = ambient
    return env


def run_case(base, production, name, ambient, fail_seed):
    root = base / name
    env = fixture(root, production, ambient, fail_seed)
    result = subprocess.run(["sh", "scripts/bootstrap/phase-ladder-step.shs",
                             PLATFORM, "in", "out", "1"], cwd=root, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
    (root / "runner.stdout").write_bytes(result.stdout)
    (root / "runner.stderr").write_bytes(result.stderr)
    observed = dict(line.split("=", 1) for line in
                    (root / "seed-env").read_text(encoding="utf-8").splitlines())
    assert observed == {"SIMPLE_NO_STUB_FALLBACK": "1", "SIMPLE_BOOTSTRAP": "1"}, observed
    assert (root / "cargo-count").read_text() == "2\n"
    assert len((root / "cargo-calls").read_text().splitlines()) == 2
    phases = list((root / "out").glob("*/PHASE"))
    github_output = root / "github-output"
    if fail_seed:
        assert result.returncode != 0, (name, result.returncode, result.stderr)
        assert not phases, (name, phases)
        assert (root / "build/ladder/evidence/seed-native-failure.sdn").is_file()
        assert "exit_status: 73" in (root / "build/ladder/evidence/seed-native-failure.sdn").read_text()
        assert not github_output.exists() or "phase=" not in github_output.read_text()
    else:
        assert result.returncode == 0, (name, result.returncode, result.stderr)
        assert len(phases) == 1, phases
        assert phases[0].read_text() == "1\n"
        assert (root / "build/ladder/evidence/hello/exit-status").read_text() == "0\n"
        assert (root / "out/linux-x86_64-p1/simple").is_file()
    return name


def main():
    production = REPO / "scripts/bootstrap/phase-ladder-step.shs"
    base = Path(tempfile.mkdtemp(prefix="phase-ladder-strict-seed-"))
    print("evidence=" + str(base), flush=True)
    cases = [("unset-reject", None, True), ("zero-reject", "0", True),
             ("zero-qualified-fixture", "0", False)]
    for name, ambient, fail_seed in cases:
        print("PASS " + run_case(base, production, name, ambient, fail_seed), flush=True)
    print("PASS: 3 controlled seed-command harness cases; no compiler qualification")


if __name__ == "__main__":
    main()
