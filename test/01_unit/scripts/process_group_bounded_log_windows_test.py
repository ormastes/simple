#!/usr/bin/env python3
"""Actual Windows process/descendant faults for the bootstrap host collector."""

import ctypes
from ctypes import wintypes
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


def fixture(mode, target):
    if mode in ("descendant", "overflow"):
        child = subprocess.Popen([sys.executable, __file__, "--fixture", "sleep", str(target)],
                                 stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        target.write_text(str(child.pid), encoding="ascii")
        if mode == "overflow":
            os.write(1, b"x" * 2000000)
    elif mode == "sleep":
        time.sleep(30)
    elif mode == "exception":
        ctypes.WinDLL("kernel32").ExitProcess(0xC0000005)
    elif mode == "mutate":
        with target.open("ab") as stream:
            stream.write(b"\n# changed while collector runs\n")
    elif mode == "collision":
        target.write_text("late sentinel", encoding="ascii")
    elif mode == "marker":
        target.write_text("child executed", encoding="ascii")
    else:
        os.write(1, b"stdout\n")
        os.write(2, b"stderr\n")
        return 7
    return 0


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dead(pid):
    kernel = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel.OpenProcess.restype = wintypes.HANDLE
    kernel.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
    kernel.CloseHandle.argtypes = [wintypes.HANDLE]
    process = kernel.OpenProcess(0x100000, False, pid)
    if not process:
        return ctypes.get_last_error() == 87
    try:
        return kernel.WaitForSingleObject(process, 0) == 0
    finally:
        kernel.CloseHandle(process)


def main():
    if os.name != "nt":
        raise RuntimeError("this regression requires actual Windows execution")
    root = Path(__file__).resolve().parents[3]
    helper = root / "scripts/bootstrap/run-process-group-bounded-log-windows.py"
    evidence = root / "build/native_probe/stage2-sanity-windows"
    evidence.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="collector-regression-", dir=evidence))
    checks = []

    def run(name, mode, target=None, expected=0, cap=4096, timeout=5, collector=helper):
        command = [sys.executable, str(collector), f"--output-parent={work}",
                   f"--log-leaf={name}.log", f"--receipt-leaf={name}.env",
                   f"--max-bytes={cap}", f"--timeout-seconds={timeout}",
                   "--term-grace-seconds=1", f"--helper-sha256={sha(collector)}", "--",
                   sys.executable, str(Path(__file__).resolve()), "--fixture", mode,
                   str(target or work / f"{name}.target")]
        started = time.monotonic()
        result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
        (work / f"{name}.driver.log").write_bytes(result.stdout)
        assert result.returncode == expected, (name, result.returncode, result.stdout.decode(errors="replace"))
        elapsed = round(time.monotonic() - started, 3)
        checks.append({"case": name, "status": "pass", "exit_status": result.returncode, "elapsed_seconds": elapsed})
        receipt = work / f"{name}.env"
        if receipt.exists():
            values = dict(line.split("=", 1) for line in receipt.read_text().splitlines())
            assert values["log_sha256"] == sha(work / f"{name}.log"), name
            assert values["helper_sha256"] == sha(collector), name
            assert values["process_group"] == "windows-job", name
            assert int(values["raw_status"]) == expected, name
            assert int(values["bytes_captured"]) == (work / f"{name}.log").stat().st_size <= cap, name
            return values
        assert expected == 126, (name, "missing receipt")
        return {}

    try:
        normal = run("normal", "normal", expected=7)
        assert normal["native_exit_status"] == "7" and normal["reason"] == "child-exit"
        assert (work / "normal.log").read_bytes() == b"stdout\nstderr\n"
        for mode, expected in (("descendant", 124), ("overflow", 125)):
            pid_file = work / f"{mode}.pid"
            receipt = run(mode, mode, pid_file, expected=expected, cap=1024, timeout=2)
            assert receipt["reason"] == ("timeout" if mode == "descendant" else "overflow")
            assert dead(int(pid_file.read_text())), f"native {mode} descendant survived"
        assert (work / "overflow.log").stat().st_size == 1024
        exact = run("exact-exit", "exception", expected=139)
        assert exact["reason"] == "child-native-exception" and exact["native_exit_status"] == "3221225477"

        (work / "collision.log").write_text("original sentinel", encoding="ascii")
        marker = work / "collision.marker"
        run("collision", "marker", marker, expected=126)
        assert not marker.exists() and not (work / "collision.env").exists()
        assert (work / "collision.log").read_text() == "original sentinel"
        run("late-collision", "collision", work / "late-collision.log", expected=126)
        assert (work / "late-collision.log").read_text() == "late sentinel"
        assert not (work / "late-collision.env").exists()

        # Change the actual assignment call, keeping its source hash honest.
        # If containment fails, the suspended child's marker must remain absent.
        faulty = work / "assignment-failure.py"
        original = helper.read_text(encoding="utf-8")
        old = 'require(assign(job, process.process), "assign suspended child to job")'
        assert original.count(old) == 1
        faulty.write_text(original.replace(old, 'raise RuntimeError("injected assignment failure")'), encoding="utf-8")
        assignment_marker = work / "assignment.marker"
        run("assignment-failure", "marker", assignment_marker, expected=126, collector=faulty)
        assert not assignment_marker.exists() and not (work / "assignment-failure.env").exists()

        mutable = work / "mutable-helper.py"
        mutable.write_bytes(helper.read_bytes())
        run("helper-mutation", "mutate", mutable, expected=126, collector=mutable)
        assert not (work / "helper-mutation.env").exists()
        assert not list(work.glob(".*.tmp.*")), "unpublished temporary leaked"
    finally:
        (work / "results.json").write_text(json.dumps({"host": sys.platform, "helper_sha256": sha(helper),
                                                      "checks": checks}, indent=2) + "\n", encoding="utf-8")
        print(f"evidence={work}")
    print(f"PASS: {len(checks)} actual Windows bounded collector cases")


if __name__ == "__main__":
    if sys.argv[1:2] == ["--fixture"]:
        sys.exit(fixture(sys.argv[2], Path(sys.argv[3])))
    main()
