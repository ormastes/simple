#!/usr/bin/env python3
"""Actual POSIX shell discovery controls; fixture handoffs are not qualified compilers."""
import argparse
import concurrent.futures
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import re
import textwrap


CASES = [
    ("empty", None, True, None),
    ("lookup-error", None, False, None),
    ("lookup-error", 3, True, 3),
    ("lookup-error", 2, True, 2),
    ("download-error", None, False, None),
    ("download-error", 3, True, 3),
    ("download-error", 2, True, 2),
    ("resume", None, True, 3),
    ("mixed", None, True, 3),
    ("invalid-artifact", None, False, None),
    ("resume", "invalid", False, None),
    ("lookup-reject", 3, True, 3),
    ("rejected", None, True, None),
    ("rejected-older-valid", None, True, 3),
    ("rejected-foreign", None, False, None),
    ("rejected-phase", None, False, None),
    ("rejected-extra", None, False, None),
    ("candidate-bound", None, False, None),
    ("download-error-older-valid", None, True, 3),
    ("invalid-run", None, False, None),
]


def check(base, production, shell, platform, index, case):
    scenario, local_phase, accepted, expected_phase = case
    root = base / (platform + "-" + str(index))
    root.mkdir()
    fakebin = root / "bin"
    fakebin.mkdir()
    gh = fakebin / "gh"
    gh.write_text("""#!/bin/sh
set -eu
echo "$1" >> "$FIXTURE_ROOT/calls"
if [ "$1" = api ]; then
  case "$SCENARIO" in
    lookup-error|lookup-reject) echo 'unexpected end of JSON input' >&2; exit 1 ;;
    mixed)
      case "$2" in *-r4*) echo 'service unavailable' >&2; exit 1 ;; esac ;;
  esac
  case "$2" in
    *-r3*)
      case "$SCENARIO" in
        download-error|resume|mixed|invalid-artifact) echo 123 ;;
        invalid-run) echo 'not a run ID' ;;
        rejected|rejected-foreign|rejected-phase|rejected-extra) echo 200 ;;
        rejected-older-valid|download-error-older-valid) printf '200\\n123\\n' ;;
        candidate-bound) printf '200\\n201\\n202\\n203\\n204\\n' ;;
      esac ;;
  esac
  exit 0
fi
[ "$1:$2" = 'run:download' ]
run_id=$3
echo "download:$run_id" >> "$FIXTURE_ROOT/calls"
shift 3
destination=
while [ "$#" -gt 0 ]; do
  case "$1" in -D) destination=$2; shift 2 ;; *) shift ;; esac
done
[ -n "$destination" ]
mkdir -p "$destination"
if [ "$SCENARIO" = download-error ] || { [ "$SCENARIO" = download-error-older-valid ] && [ "$run_id" = 200 ]; }; then
  echo 'partial bytes' > "$destination/partial"
  echo 'artifact download failed' >&2
  exit 1
fi
if [ "$run_id" != 123 ]; then
  rejected="$destination/$PLATFORM-rejected-p1"
  if [ "$SCENARIO" = rejected-foreign ]; then rejected="$destination/foreign-x86_64-rejected-p1"; fi
  mkdir -p "$rejected"
  printf 'rejected diagnostic fixture bytes\\n' > "$rejected/simple$EXE"
  if [ "$SCENARIO" = rejected-phase ]; then echo 1 > "$rejected/PHASE"; fi
  if [ "$SCENARIO" = rejected-extra ]; then echo unexpected > "$rejected/extra"; fi
  exit 0
fi
if [ "$SCENARIO" = invalid-artifact ]; then
  mkdir -p "$destination/$PLATFORM-p3"
  echo 3 > "$destination/$PLATFORM-p3/PHASE"
  exit 0
fi
mkdir -p "$destination/$PLATFORM-p3"
echo 3 > "$destination/$PLATFORM-p3/PHASE"
printf 'shell fixture, not a compiler\\n' > "$destination/$PLATFORM-p3/simple$EXE"
""", encoding="utf-8", newline="\n")
    gh.chmod(0o755)
    in_dir = root / "in"
    in_dir.mkdir()
    evidence = in_dir / ".resume-evidence"
    evidence.mkdir()
    marker = evidence / (platform + ".incomplete.sdn")
    marker.write_text("previous diagnostic marker\n")
    exe = ".exe" if platform.startswith("windows-") else ""
    if local_phase is not None:
        phase = 3 if local_phase == "invalid" else local_phase
        handoff = in_dir / (platform + "-p" + str(phase))
        handoff.mkdir()
        (handoff / "PHASE").write_text(str(phase) + "\n")
        if local_phase != "invalid":
            (handoff / ("simple" + exe)).write_bytes(b"existing parent bytes\n")
    shutil.copyfile(production, root / "resume.shs")
    env = os.environ.copy()
    env.update(PATH=str(fakebin) + os.pathsep + env["PATH"],
               FIXTURE_ROOT=str(root), SCENARIO=scenario, PLATFORM=platform, EXE=exe,
               GITHUB_REPOSITORY="fixture/repo", GITHUB_REF_NAME="fixture-branch")
    result = subprocess.run([shell, "resume.shs", "in", platform], cwd=root, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=15)
    (root / "stdout").write_bytes(result.stdout)
    (root / "stderr").write_bytes(result.stderr)
    assert (result.returncode == 0) == accepted, (platform, case, result.stderr)
    calls = (root / "calls").read_text().splitlines()
    assert calls.count("api") == 4, calls  # One finite pass, no retry loop.
    downloads = 2 if scenario in ("rejected-older-valid", "download-error-older-valid") else (
        4 if scenario == "candidate-bound" else (
            0 if scenario in ("empty", "lookup-error", "lookup-reject", "invalid-run") else 1))
    assert calls.count("run") == downloads, calls
    if scenario in ("rejected-older-valid", "download-error-older-valid"):
        assert [line for line in calls if line.startswith("download:")] == ["download:200", "download:123"], calls
    if scenario == "candidate-bound":
        assert "download:204" not in calls
        assert b"candidate limit reached" in result.stderr
    if expected_phase is not None:
        expected = in_dir / (platform + "-p" + str(expected_phase)) / ("simple" + exe)
        expected_bytes = b"existing parent bytes\n" if local_phase else b"shell fixture, not a compiler\n"
        assert expected.read_bytes() == expected_bytes, case
    else:
        assert not list(in_dir.glob(platform + "-p*/simple*")), case
    incomplete = scenario not in ("empty", "resume", "rejected", "rejected-older-valid") or local_phase == "invalid"
    assert marker.exists() == incomplete, case
    if incomplete:
        assert "admission: none" in marker.read_text(), case
    if scenario in ("lookup-error", "lookup-reject"):
        assert "unexpected end of JSON input" in (evidence / ("ladder-" + platform + "-r4.lookup.stderr")).read_text()
    if scenario == "download-error":
        assert "artifact download failed" in (evidence / ("ladder-" + platform + "-r3-123.download.stderr")).read_text()
        assert (in_dir / (".resume-ladder-" + platform + "-r3-123") / "partial").is_file()
    if not accepted:
        assert b"refusing cold seed fallback" in result.stderr, result.stderr
    if scenario == "resume" and local_phase == "invalid":
        assert (evidence / ("ladder-" + platform + "-r3-123.download") /
                (platform + "-p3") / ("simple" + exe)).is_file()
        assert b"from run" not in result.stdout
    if scenario in ("rejected", "rejected-older-valid"):
        rejected = evidence / ("ladder-" + platform + "-r3-200.download") / (platform + "-rejected-p1")
        assert (rejected / ("simple" + exe)).read_bytes() == b"rejected diagnostic fixture bytes\n"
        assert not (rejected / "PHASE").exists()
        assert b"admission=none" in result.stdout
        assert not list(in_dir.glob(platform + "-rejected-*"))
    if scenario == "lookup-reject":
        # A PHASE-shaped candidate is not qualification. The real ladder must
        # try the parent, then preserve discovery failure instead of cold seed.
        scripts = root / "scripts/bootstrap"
        scripts.mkdir(parents=True)
        shutil.copyfile(production.with_name("phase-ladder-step.shs"), scripts / "phase-ladder-step.shs")
        (scripts / "build-next-phase-ci.shs").write_text(
            "#!/bin/sh\nprintf attempted > parent-attempted\nexit 1\n")
        env["PHASE_LADDER_SELFHOST_THREADS"] = "24"
        rejected = subprocess.run([shell, "scripts/bootstrap/phase-ladder-step.shs", platform,
                                   "in", "out", "24"], cwd=root, env=env,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=15)
        (root / "step.stdout").write_bytes(rejected.stdout)
        (root / "step.stderr").write_bytes(rejected.stderr)
        assert (root / "parent-attempted").read_text() == "attempted"
        assert rejected.returncode != 0
        assert b"parent attempt failed after incomplete discovery" in rejected.stderr, rejected.stderr
        assert not list((root / "out").glob("*/PHASE"))
    return platform + ":" + scenario + ":local=" + str(local_phase)


def retention_and_upload(base, production, shell, platform):
    root = base / (platform + "-retention-upload")
    root.mkdir()
    source = production.with_name("phase-ladder-step.shs").read_text()
    matched = re.search(r"^retain_rejected_candidate\(\) \{\n.*?^\}", source, re.M | re.S)
    assert matched, "real retention owner missing"
    exe = ".exe" if platform.startswith("windows-") else ""
    sentinel = b"non-executable diagnostic byte sentinel\n"
    (root / "candidate").write_bytes(sentinel)
    code = ("set -eu\nevidence_root=build/ladder/evidence\nplatform=" + platform +
            "\nnext=1\nexe=" + exe + "\nbin=candidate\n" + matched.group() +
            "\nretain_rejected_candidate hello-run-failed\n")
    script = root / "retain.shs"
    script.write_text(code, newline="\n")
    result = subprocess.run([shell, "retain.shs"], cwd=root, capture_output=True, timeout=15)
    assert result.returncode == 0, result.stderr
    rejected = root / "build/ladder/evidence/rejected" / (platform + "-rejected-p1")
    assert (rejected / ("simple" + exe)).read_bytes() == sentinel
    assert "admission: none\nreason: hello-run-failed\n" in (rejected / "REJECTED.sdn").read_text()
    assert not (rejected / "PHASE").exists()
    assert not (root / "build/ladder/out").exists()
    workflow = production.parents[2] / ".github/workflows/phase-ladder-rung.yml"
    lines = workflow.read_text().splitlines()
    gates = []
    for index, line in enumerate(lines):
        if line.strip() != "- name: Detect retained proven handoffs":
            continue
        while lines[index].strip() != "run: |":
            index += 1
        index += 1
        body = []
        while index < len(lines) and lines[index].startswith("          "):
            body.append(lines[index])
            index += 1
        gates.append(textwrap.dedent("\n".join(body)) + "\n")
    assert len(gates) == 2 and gates[0] == gates[1]
    gate = root / "gate.shs"
    gate.write_text(gates[0], newline="\n")
    output = root / "github-output"
    env = dict(os.environ, PLATFORM=platform, GITHUB_OUTPUT=str(output))
    # A legacy rejected-only out/ tree cannot create a proven artifact.
    legacy = root / "build/ladder/out" / (platform + "-rejected-p1")
    legacy.mkdir(parents=True)
    (legacy / ("simple" + exe)).write_bytes(sentinel)
    result = subprocess.run([shell, "gate.shs"], cwd=root, env=env, capture_output=True, timeout=15)
    assert result.returncode == 0 and output.read_text() == "available=false\n", result.stderr
    output.unlink()
    admitted_shape = root / "build/ladder/out" / (platform + "-p3")
    admitted_shape.mkdir()
    (admitted_shape / "PHASE").write_text("3\n")
    (admitted_shape / ("simple" + exe)).write_bytes(sentinel)
    result = subprocess.run([shell, "gate.shs"], cwd=root, env=env, capture_output=True, timeout=15)
    assert result.returncode == 0 and output.read_text() == "available=true\n", result.stderr
    # Metadata/retention only. These sentinels are never compiler admission.
    return platform + ":actual-retention-owner-and-workflow-metadata"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=24)
    parser.add_argument("--shell", default="sh")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("positive --jobs required")
    production = Path(__file__).resolve().parents[1] / "phase-ladder-resume.shs"
    base = Path(tempfile.mkdtemp(prefix="phase-ladder-resume-"))
    print("evidence=" + str(base), flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(check, base, production, args.shell, platform, index, case)
                   for platform in ("linux-x86_64", "windows-x86_64")
                   for index, case in enumerate(CASES)]
        futures += [pool.submit(retention_and_upload, base, production, args.shell, platform)
                    for platform in ("linux-x86_64", "windows-x86_64")]
        for future in futures:
            print("PASS " + future.result())
    print(f"PASS: {len(CASES) * 2} discovery cases + 2 retention/upload cases; jobs={args.jobs}; no compiler qualification or build")


if __name__ == "__main__":
    main()
