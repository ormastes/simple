#!/usr/bin/env python3
"""Actual POSIX shell discovery controls; fixture handoffs are not qualified compilers."""
import argparse
import concurrent.futures
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


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
      esac ;;
  esac
  exit 0
fi
[ "$1:$2:$3" = 'run:download:123' ]
shift 3
destination=
while [ "$#" -gt 0 ]; do
  case "$1" in -D) destination=$2; shift 2 ;; *) shift ;; esac
done
[ -n "$destination" ]
mkdir -p "$destination"
if [ "$SCENARIO" = download-error ]; then
  echo 'partial bytes' > "$destination/partial"
  echo 'artifact download failed' >&2
  exit 1
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
    assert calls.count("run") == (1 if scenario in ("download-error", "resume", "mixed", "invalid-artifact") else 0), calls
    if expected_phase is not None:
        expected = in_dir / (platform + "-p" + str(expected_phase)) / ("simple" + exe)
        expected_bytes = b"existing parent bytes\n" if local_phase else b"shell fixture, not a compiler\n"
        assert expected.read_bytes() == expected_bytes, case
    else:
        assert not list(in_dir.glob(platform + "-p*/simple*")), case
    incomplete = scenario not in ("empty", "resume") or local_phase == "invalid"
    assert marker.exists() == incomplete, case
    if incomplete:
        assert "admission: none" in marker.read_text(), case
    if scenario in ("lookup-error", "lookup-reject"):
        assert "unexpected end of JSON input" in (evidence / ("ladder-" + platform + "-r4.lookup.stderr")).read_text()
    if scenario == "download-error":
        assert "artifact download failed" in (evidence / ("ladder-" + platform + "-r3.download.stderr")).read_text()
        assert (in_dir / (".resume-ladder-" + platform + "-r3") / "partial").is_file()
    if not accepted:
        assert b"refusing cold seed fallback" in result.stderr, result.stderr
    if scenario == "resume" and local_phase == "invalid":
        assert (in_dir / (".resume-ladder-" + platform + "-r3") /
                (platform + "-p3") / ("simple" + exe)).is_file()
        assert b"from run" not in result.stdout
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
        for future in futures:
            print("PASS " + future.result())
    print("PASS: 24 shell discovery controls; no compiler qualification or build")


if __name__ == "__main__":
    main()
