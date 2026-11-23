#!/usr/bin/env python3
"""Exercise the actual phase-ladder seed command with controlled shell tools.

These fixtures verify runner environment forwarding and failure/handoff control
flow only. The failing seed fixture models a strict unresolved-return link
failure; it does not exercise actual alias resolution. The passing fixture does
not compile Simple or qualify a compiler.
"""
import os
from pathlib import Path
import re
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


def resolver_contract(base):
    """Mock wrapper contract only: no Simple compilation or qualification."""
    root = base / "resolver-checkout"
    root.mkdir()
    caller = root / "caller"
    caller.mkdir()
    external = base / "external-resolver-work"
    external.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    compiler = root / "mock-compiler"
    write_script(compiler, """#!/bin/sh
set -eu
caller_root=$(git rev-parse --show-toplevel)
caller_root=$(cd "$caller_root" && pwd -P)
[ "$(pwd -P)" = "$caller_root" ] || { echo 'mock SCV: CWD is not checkout root' >&2; exit 46; }
[ "$1" != --version ] || { echo 'mock-contract-only'; exit 0; }
[ "$1" = native-build ] && [ "$3" = -o ] && [ "$#" = 4 ]
entry=$(cd "$(dirname "$2")" && printf '%s/%s' "$(pwd -P)" "$(basename "$2")")
case "$entry" in "$caller_root"/*) ;; *) echo 'mock SCV: source outside caller checkout' >&2; exit 42 ;; esac
grep -Fq 'print "bootstrap-compiler-probe"' "$entry"
printf '%s\\n' "${entry#"$caller_root"/}" >> "$caller_root/source-relative"
case ${SIMPLE_CACHE_SCOPE:-} in bootstrap-compiler-probe.*) ;; *) exit 45 ;; esac
printf '%s\\n' "$SIMPLE_CACHE_SCOPE" >> "$caller_root/cache-scopes"
[ "${FIXTURE_PROBE_FAIL:-}" != build ] || { echo 'mock build rejection'; exit 43; }
cat > "$4" <<'PROGRAM'
#!/bin/sh
hello_root=$(git rev-parse --show-toplevel)
[ "$(pwd -P)" = "$(cd "$hello_root" && pwd -P)" ] || exit 46
if [ "${FIXTURE_PROBE_FAIL:-}" = output ]; then echo 'wrong-marker'; exit 0; fi
if [ "${FIXTURE_PROBE_FAIL:-}" = stderr ]; then echo 'bootstrap-compiler-probe' >&2; exit 0; fi
if [ "${FIXTURE_PROBE_FAIL:-}" = diagnostic ]; then echo 'diagnostic mentions bootstrap-compiler-probe'; exit 0; fi
if [ "${FIXTURE_PROBE_FAIL:-}" = extra ]; then printf 'bootstrap-compiler-probe\\nextra-output\\n'; exit 0; fi
if [ "${FIXTURE_PROBE_FAIL:-}" = embedded-cr ]; then printf 'bootstrap-compiler-\\rprobe\\n'; exit 0; fi
if [ "${FIXTURE_PROBE_FAIL:-}" = crlf ]; then printf 'bootstrap-compiler-probe\\r\\n'; exit 0; fi
echo 'bootstrap-compiler-probe'
[ "${FIXTURE_PROBE_FAIL:-}" != run ] || exit 44
PROGRAM
chmod +x "$4"
""")
    env = os.environ.copy()
    env.update(SIMPLE_BOOTSTRAP_COMPILER="../mock-compiler",
               SIMPLE_BOOTSTRAP_COMPILER_PHASE="3")
    resolver = REPO / "scripts/bootstrap/resolve-bootstrap-compiler.shs"
    for failure in ("", "", "build", "run", "output", "stderr", "diagnostic",
                    "extra", "embedded-cr", "crlf"):
        env["FIXTURE_PROBE_FAIL"] = failure
        result = subprocess.run(["sh", str(resolver), "--platform", PLATFORM,
                                 "--config", str(root / "missing.sdn"),
                                 "--work-dir", os.path.relpath(external, caller).replace(os.sep, "/")], cwd=caller, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        if failure and failure != "crlf":
            assert result.returncode == 1, (failure, result.returncode, result.stderr)
            assert not result.stdout, result.stdout
        else:
            assert result.returncode == 0, result.stderr
            assert result.stdout.decode().strip() == "../mock-compiler 3"
    sources = (root / "source-relative").read_text().splitlines()
    assert len(sources) == 10 and len(set(sources)) == 10, sources
    scopes = (root / "cache-scopes").read_text().splitlines()
    assert len(scopes) == 10 and len(set(scopes)) == 10, scopes
    for source in sources:
        path = root / source
        assert path.is_file() and path.resolve().is_relative_to(root.resolve()), path
        assert path.name == "hello.spl"
    probes = list(external.glob("probe.*"))
    assert len(probes) == 10, probes
    assert all((probe / "source-path").is_file() and (probe / "build.log").is_file()
               for probe in probes)
    assert sum((probe / "run.log").is_file() for probe in probes) == 9
    assert sum((probe / "run.stderr").is_file() for probe in probes) == 9
    statuses = sorted((probe / "run-exit-status").read_text().strip()
                      for probe in probes if (probe / "run-exit-status").is_file())
    assert statuses == ["0"] * 8 + ["44"], statuses
    outside = external / "outside.spl"
    outside.write_text('fn main():\n    print "bootstrap-compiler-probe"\n')
    negative = subprocess.run(["sh", str(compiler), "native-build", str(outside),
                               "-o", str(external / "must-not-exist")],
                              cwd=root, env=env, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=30)
    assert negative.returncode == 42 and b"source outside caller checkout" in negative.stderr
    assert not (external / "must-not-exist").exists()
    wrong_cwd = subprocess.run(["sh", str(compiler), "native-build", str(root / sources[0]),
                                "-o", str(external / "must-not-exist")],
                               cwd=caller, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, timeout=30)
    assert wrong_cwd.returncode == 46 and b"CWD is not checkout root" in wrong_cwd.stderr
    assert not (external / "must-not-exist").exists()
    print("PASS: resolver mock contract: caller checkout source, unique retained probes, "
          "build/run/stdout-marker rejection, CRLF and independent SCV negative; no compiler qualification",
          flush=True)


def next_phase_sharding_contract(base):
    """Exercise the real CI wrapper with a refusing mock, not a compiler."""
    production = (REPO / "scripts/bootstrap/build-next-phase-ci.shs").read_text()
    assert production.count("SIMPLE_PARSE_SHARDING=1") == 1
    ladder = (REPO / "scripts/bootstrap/phase-ladder-step.shs").read_text()
    assert "SIMPLE_PARSE_SHARDING=0" not in ladder
    assert ladder.count("SIMPLE_PARSE_SHARDING=1") == 2
    for disabled in (False, True):
        root = base / ("old-disabled" if disabled else "ordinary-sharding")
        root.mkdir(parents=True)
        wrapper = root / "scripts/bootstrap/build-next-phase-ci.shs"
        write_script(wrapper, production.replace("SIMPLE_PARSE_SHARDING=1", "SIMPLE_PARSE_SHARDING=0")
                     if disabled else production)
        write_script(root / "scripts/bootstrap/resolve-bootstrap-compiler.shs", """#!/bin/sh
printf '%s 1\\n' "$FIXTURE_ROOT/mock-builder"
""")
        write_script(root / "mock-builder", """#!/bin/sh
set -eu
[ "$1" = native-build ]
printf '%s\\n' "${SIMPLE_PARSE_SHARDING-unset}" > "$FIXTURE_ROOT/parse-policy"
[ "${SIMPLE_PARSE_SHARDING:-}" = 1 ] && [ "${SIMPLE_HIR_SHARDING:-}" != 0 ] || {
  echo 'mock pool refusal: HIR disabled' >&2; exit 67;
}
[ "${SIMPLE_BOOTSTRAP_WHOLE_PROGRAM:-}" != 1 ] || exit 68
output= requested= cache=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --output) output=$2; shift 2 ;;
    --threads) requested=$2; shift 2 ;;
    --cache-dir) cache=$2; shift 2 ;;
    *) shift ;;
  esac
done
[ "$requested" = 4 ] && [ "$output" = build/bootstrap/stage2/simple ]
[ "${cache##*/}" = phase2 ]
printf '%s\\n' "$requested" > "$FIXTURE_ROOT/selected-threads"
cp "$FIXTURE_ROOT/mock-result" "$output"
chmod +x "$output"
""")
        write_script(root / "mock-result", """#!/bin/sh
[ "$1" = --version ]
echo 'mock next phase: contract only'
""")
        env = os.environ.copy()
        env.update(FIXTURE_ROOT=str(root), SIMPLE_PARSE_SHARDING="0",
                   GITHUB_ENV=str(root / "github-env"), GITHUB_OUTPUT=str(root / "github-output"))
        env.pop("SIMPLE_BOOTSTRAP_WHOLE_PROGRAM", None)
        env.pop("SIMPLE_HIR_SHARDING", None)
        result = subprocess.run(["sh", "scripts/bootstrap/build-next-phase-ci.shs", PLATFORM, "4"],
                                cwd=root, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=30)
        if disabled:
            assert result.returncode == 1 and b"mock pool refusal" in result.stderr, result.stderr
            assert (root / "parse-policy").read_text().strip() == "0"
            assert not (root / "github-output").exists()
            assert not (root / "build/bootstrap/stage2/simple").exists()
        else:
            assert result.returncode == 0, (result.stdout, result.stderr)
            assert (root / "parse-policy").read_text().strip() == "1"
            assert (root / "selected-threads").read_text().strip() == "4"
            assert (root / "github-output").read_text().strip() == "built=true"
            assert "BUILT_PHASE=2" in (root / "github-env").read_text()
    print("PASS: CI wrapper sharding mock contract: disabled policy rejects, ordinary pool "
          "preserves selected threads and handoff; no compiler qualification", flush=True)


def ladder_rung_budget_contract():
    """Evaluate actual workflow guard expressions; no Actions/build execution."""
    source = (REPO / ".github/workflows/phase-ladder.yml").read_text()
    budget = re.search(r"^      max_rung:\n((?:        .*\n)+)", source, re.M).group(1)
    assert "type: choice" in budget and "default: '4'" in budget
    assert "options: ['1', '2', '3', '4']" in budget
    assert "if: always() && (github.event_name != 'workflow_dispatch' || inputs.publish)" in source

    def check(text):
        for chain in ("", "slow-"):
            for rung in (2, 3, 4):
                block = re.search(r"^  " + chain + "rung" + str(rung) +
                                  r":\n((?:    .*\n)+)", text, re.M).group(1)
                guard = re.search(r"^    if: (.*)$", block, re.M).group(1)
                expression = guard.replace("always()", "True")
                expression = expression.replace("fromJSON(inputs.max_rung)", "int(limit)")
                expression = expression.replace("github.event_name", "event").replace("inputs.max_rung", "limit")
                expression = re.sub(r"needs\.slow-rung[1-3]\.result", "previous", expression)
                expression = expression.replace("&&", " and ").replace("||", " or ")
                for event in ("push", "schedule", "workflow_dispatch"):
                    for limit in ("", "1", "2", "3", "4"):
                        for previous in ("success", "failure", "skipped"):
                            selected = bool(eval(expression, {"__builtins__": {}, "int": int},
                                                 dict(event=event, limit=limit, previous=previous)))
                            expected = (event != "workflow_dispatch" or not limit or rung <= int(limit))
                            if chain:
                                expected = expected and previous != "skipped"
                            assert selected == expected, (chain, rung, event, limit, previous, guard)
    check(source)
    try:
        check(source.replace("fromJSON(inputs.max_rung) >= 2", "fromJSON(inputs.max_rung) >= 1", 1))
    except AssertionError:
        pass
    else:
        raise AssertionError("budget contract accepted an extra rung for max_rung=1")
    print("PASS: workflow rung budget guard contract: manual 1-4, legacy default4, "
          "push/schedule and slow-chain skip policy; no Actions/compiler execution", flush=True)


def main():
    production = REPO / "scripts/bootstrap/phase-ladder-step.shs"
    base = Path(tempfile.mkdtemp(prefix="phase-ladder-strict-seed-"))
    print("evidence=" + str(base), flush=True)
    cases = [("unset-reject", None, True), ("zero-reject", "0", True),
             ("zero-qualified-fixture", "0", False)]
    for name, ambient, fail_seed in cases:
        print("PASS " + run_case(base, production, name, ambient, fail_seed), flush=True)
    resolver_contract(base)
    next_phase_sharding_contract(base)
    ladder_rung_budget_contract()
    print("PASS: 3 controlled seed-command harness cases; no compiler qualification")


if __name__ == "__main__":
    main()
