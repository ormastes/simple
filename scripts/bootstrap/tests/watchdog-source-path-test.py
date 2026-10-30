#!/usr/bin/env python3
"""Real watchdog/source-path integration; no fixture helper, protocol, or cap bypass.

Windows: native Git/MSYS Perl, a real Clang-built PE, and the canonical C
session helper. POSIX: a literal backslash directory and the real POSIX helper.
"""
import argparse
import concurrent.futures
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def fields(path):
    rows = path.read_text().splitlines()
    result = dict(row.split("=", 1) for row in rows)
    assert len(result) == len(rows), "duplicate receipt key"
    return result


def source_tree(base, production, name, missing=False):
    root = base / name
    runner = root / "scripts/resource/process-tree-rss-watchdog.pl"
    runner.parent.mkdir(parents=True)
    shutil.copyfile(production, runner)
    bootstrap = root / "scripts/bootstrap"
    bootstrap.mkdir()
    if not missing:
        shutil.copyfile(production.parent.parent / "bootstrap/bootstrap-session-exec.c",
                        bootstrap / "bootstrap-session-exec.c")
    return runner


def windows_spelling(path, spelling):
    value = str(path.resolve())
    if spelling == "back": return value.replace("/", "\\")
    if spelling == "forward": return value.replace("\\", "/")
    if spelling == "mixed":
        return value.replace("\\", "/").replace("/scripts/resource/", "/scripts\\resource\\")
    return "scripts\\resource\\process-tree-rss-watchdog.pl"


def receipt_spelling(path, cwd, spelling):
    value = str(path.resolve()).replace("\\", "/")
    if spelling == "back": return value.replace("/", "\\")
    if spelling == "mixed": return value.rsplit("/", 1)[0] + "\\" + path.name
    if spelling == "relative": return os.path.relpath(path, cwd).replace("/", "\\")
    return value


def run_case(base, production, args, runners, children, spelling, spaces, outcome, before=False):
    label = spelling + ("-spaces" if spaces else "-plain") + "-" + outcome
    evidence = base / ("evidence-" + label)
    evidence.mkdir()
    missing = outcome == "missing"
    runner = source_tree(base, production, "missing-" + label, True) if missing else runners[spaces]
    receipt = evidence / "rss.env"
    env = os.environ.copy()
    # New session, genuine compiler, default source-derived cache. No test RSS
    # facts or externally supplied session contract/helper binary is accepted.
    for key in list(env):
        if key.startswith("SIMPLE_BOOTSTRAP_SESSION_") or key.startswith("SIMPLE_PROCESS_TREE_"):
            env.pop(key)
    env["CC"] = args.cc
    cwd = runner.parent.parent.parent
    original_sources = {p.relative_to(cwd).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in cwd.rglob("*") if p.is_file() and ".simple" not in p.relative_to(cwd).parts}
    receipt_argument = receipt_spelling(receipt, cwd, spelling) if args.receipt_paths else receipt.as_posix()
    command = [args.perl, windows_spelling(runner, spelling), "--session-mode=new",
               "--rss-cap-mode=enforce", "--max-rss-kib=1048576", "--timeout-seconds=60",
               "--term-grace-seconds=5", "--receipt=" + receipt_argument, "--",
               children[37 if outcome != "zero" else 0].as_posix()]
    result = subprocess.run(command, cwd=cwd, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=90)
    (evidence / "stdout").write_bytes(result.stdout)
    (evidence / "stderr").write_bytes(result.stderr)
    actual = fields(receipt)
    if missing or (before and not args.receipt_paths):
        assert result.returncode == 89, (label, result.returncode, result.stderr)
        assert actual["status"] == "session-helper-install-failed", actual
        assert actual["root_pid"] == "0", actual
        assert b"session helper source" in result.stderr, result.stderr
        if before:
            assert (runner.parent.parent / "bootstrap/bootstrap-session-exec.c").is_file()
    else:
        expected = "0" if outcome == "zero" else "37"
        assert result.returncode == int(expected), (label, result.returncode, result.stderr)
        assert actual["status"] == "complete" and actual["exit_status"] == expected, actual
        assert int(actual["root_pid"]) > 0 and actual["quiescent"] == "1", actual
        assert actual["observer_backend"] == "win32-job-object", actual
        assert actual["rss_cap_enforced"] == "1" and actual["rss_cap_mode"] == "enforce", actual
        assert actual["session_helper_integrity"] == "verified", actual
        original = runner.parent.parent / "bootstrap/bootstrap-session-exec.c"
        assert actual["session_helper_source_sha256"] == hashlib.sha256(original.read_bytes()).hexdigest()
        # The ordinary source-relative cache must be used, with a genuine
        # installed helper and its matching hash sidecar under this root.
        cache = runner.parent.parent.parent / ".simple/storage/cache/bootstrap-session-helper"
        binaries = list(cache.glob("*/bootstrap-session-exec.exe"))
        assert len(binaries) == 1, binaries
        digest = hashlib.sha256(binaries[0].read_bytes()).hexdigest()
        assert actual["session_helper_sha256"] == digest
        assert binaries[0].with_name(binaries[0].name + ".sha256").read_text().strip() == digest
    if args.receipt_paths:
        sessions = list(evidence.glob("simple-rss-session-*"))
        misplaced = list(cwd.glob("simple-rss-session-*"))
        if before:
            assert not missing and not sessions and len(misplaced) == 1, (sessions, misplaced)
            assert (misplaced[0] / "workload.spec").is_file()
            assert fields(misplaced[0] / "workload.stats")["quiescent"] == "1"
        else:
            assert not misplaced, misplaced
            current_sources = {p.relative_to(cwd).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in cwd.rglob("*") if p.is_file() and ".simple" not in p.relative_to(cwd).parts}
            assert current_sources == original_sources, "watchdog changed source cwd"
            assert len(sessions) == (0 if missing else 1), sessions
            if not missing:
                assert (sessions[0] / "workload.spec").is_file()
                stats = fields(sessions[0] / "workload.stats")
                assert stats["quiescent"] == "1" and int(stats["root_exit_raw"], 0) == int(expected), stats
    return label


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=24)
    parser.add_argument("--perl", required=True)
    parser.add_argument("--cc", required=True)
    parser.add_argument("--pe-clang")
    parser.add_argument("--before-fix", action="store_true")
    parser.add_argument("--receipt-paths", action="store_true", help="test receipt-parent custody instead of source-path discovery")
    args = parser.parse_args()
    if args.jobs < 1: parser.error("positive --jobs required")
    production = Path(__file__).resolve().parents[2] / "resource/process-tree-rss-watchdog.pl"
    base = Path(tempfile.mkdtemp(prefix="watchdog-source-path-"))
    print("evidence=" + str(base), flush=True)
    if os.name != "nt":
        runner = source_tree(base, production, "literal\\backslash root")
        receipt_parent = base / "receipt\\literal backslash"
        receipt_parent.mkdir()
        receipt = receipt_parent / "posix.rss.env"
        env = os.environ.copy()
        env["CC"] = args.cc
        result = subprocess.run([args.perl, str(runner), "--session-mode=new", "--max-rss-kib=1048576",
                                 "--timeout-seconds=60", "--term-grace-seconds=5",
                                 "--receipt=" + str(receipt), "--", "/bin/sh", "-c", "exit 37"],
                                env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=90)
        (base / "posix.stderr").write_bytes(result.stderr)
        actual = fields(receipt)
        assert result.returncode == 37 and actual["exit_status"] == "37", (actual, result.stderr)
        assert actual["quiescent"] == "1" and actual["session_helper_integrity"] == "verified", actual
        assert len(list(receipt_parent.glob("simple-rss-session-*"))) == 1
        assert not list(runner.parent.parent.parent.glob("simple-rss-session-*"))
        print("PASS: real POSIX helper preserves literal backslash source and receipt directories")
        return
    if not args.pe_clang: parser.error("--pe-clang required on Windows")
    children = {}
    for code in (0, 37):
        source = base / ("exit-" + str(code) + ".c")
        output = source.with_suffix(".exe")
        source.write_text("unsigned int entry(void) { return " + str(code) + "u; }\n")
        built = subprocess.run([args.pe_clang, "--target=x86_64-pc-windows-msvc", "-fuse-ld=lld", "-nostdlib",
                                "-Xlinker", "/entry:entry", "-Xlinker", "/subsystem:console",
                                str(source), "-o", str(output)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        (base / ("compile-" + str(code) + ".stderr")).write_bytes(built.stderr)
        assert built.returncode == 0, built.stderr
        assert output.read_bytes()[:2] == b"MZ"
        children[code] = output
    runners = {spaces: source_tree(base, production, "source root spaces" if spaces else "source-root")
               for spaces in (False, True)}
    if args.before_fix:
        print("RED CONFIRMED " + run_case(base, production, args, runners, children, "back", False, "exit37", True))
        return
    warmups = [("forward", spaces, "exit37") for spaces in (False, True)]
    # These are two actual controls, not repeated checks: compile each genuine
    # source-derived helper cache once before the parallel tiny-process cases.
    for spelling, spaces, outcome in warmups:
        print("PASS " + run_case(base, production, args, runners, children, spelling, spaces, outcome), flush=True)
    work = [(spelling, spaces, outcome) for spelling in ("forward", "back", "mixed", "relative")
            for spaces in (False, True) for outcome in ("exit37", "zero", "missing")
            if (spelling, spaces, outcome) not in warmups]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run_case, base, production, args, runners, children, *case) for case in work]
        for future in futures: print("PASS " + future.result(), flush=True)
    print("PASS: 24 real Windows watchdog " + ("receipt-parent" if args.receipt_paths else "source-path") + " controls; genuine helper and native PE exits; no compiler qualification")


if __name__ == "__main__": main()
