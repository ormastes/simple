#!/usr/bin/env python3
"""Focused native containment gate. Execution requires explicit cycle admission.

Never launches the whole suite. Fixtures have 12-second alarms (20 seconds for
the explicitly held nested-RSS parent) even if supervision fails. An optional original pane-spec command is mandatory
for a complete qualification result; omission is reported NOT_RUN, not PASS.
"""
import argparse
import ctypes
import errno
import hashlib
import json
import os
from pathlib import Path
import signal
import select
import re
import subprocess
import sys
import time


def fixture(kind, directory):
    directory = Path(directory)
    held = kind == "nested-held" or kind.startswith("zombie-")
    signal.alarm(20 if held else 12)

    def note():
        with (directory / "pids").open("a") as out:
            out.write(f"{os.getpid()}\n")

    def sleeper(detach=True, memory_mb=0):
        signal.alarm(20 if held else 12)
        if detach:
            os.setsid()
        note()
        if memory_mb:
            allocation = bytearray(memory_mb * 1024 * 1024)
            for n in range(0, len(allocation), 4096):
                allocation[n] = 1
            temporary = directory / "allocated.json.tmp"
            temporary.write_text(json.dumps({"pid": os.getpid(), "minimum_rss_kib": memory_mb * 1024}))
            temporary.replace(directory / "allocated.json")
        time.sleep(18 if held else 10)
        os._exit(0)

    note()
    if kind in ("zombie-waitable", "zombie-held"):
        if kind == "zombie-held" and os.fork() != 0:
            # Deliberately retain the zombie under a live non-reaping parent.
            # Only the tested native owner may terminate this fixture.
            signal.pause()
            raise AssertionError("held zombie parent unexpectedly resumed")
        signal.alarm(20)
        libc = ctypes.CDLL(None, use_errno=True)
        assert libc.procctl(0, 0, 2, None) == 0, ctypes.get_errno()
        if os.fork() == 0:
            sleeper(memory_mb=32)
        until = time.monotonic() + 10
        while not (directory / "exit-reaper").exists():
            assert time.monotonic() < until, "zombie fixture release deadline"
            time.sleep(0.001)
        os._exit(7)
    if kind == "pty":
        pid, fd = os.forkpty()
        if pid == 0:
            signal.alarm(12)
            note()
            os.execl("/bin/sh", "sh", "-c", "printf PTY_OK; sleep 0.3")
        data = b""
        try:
            while True:
                part = os.read(fd, 1024)
                if not part:
                    break
                data += part
        except OSError:
            pass  # PTY master commonly returns EIO on slave close
        finally:
            os.close(fd)
        _, status = os.waitpid(pid, 0)
        assert data == b"PTY_OK" and os.waitstatus_to_exitcode(status) == 0
        return
    if kind == "kill-owner":
        os.kill(os.getppid(), signal.SIGKILL)
        return
    if kind in ("nested", "nested-held"):
        libc = ctypes.CDLL(None, use_errno=True)
        # FreeBSD sys/wait.h: P_PID is the first idtype_t member (0).
        assert libc.procctl(0, 0, 2, None) == 0, ctypes.get_errno()
    if kind == "double-fork":
        pid = os.fork()
        if pid == 0:
            signal.alarm(12)
            if os.fork() == 0:
                sleeper()
            os._exit(0)
        os.waitpid(pid, 0)
        time.sleep(0.25)
        return
    if kind == "fork-race":
        until = time.monotonic() + 8
        while time.monotonic() < until:
            if os.fork() == 0:
                sleeper()
            time.sleep(0.025)
        return
    count = 20 if kind == "twenty" else 1
    for _ in range(count):
        if os.fork() == 0:
            sleeper(memory_mb=96 if kind == "rss" else 32 if kind in ("nested", "nested-held") else 0)
    until = time.monotonic() + 2
    while len((directory / "pids").read_text().splitlines()) < count + 1 and time.monotonic() < until:
        time.sleep(0.01)
    assert len((directory / "pids").read_text().splitlines()) == count + 1
    (directory / "ready").touch()
    if kind == "nested-held":
        # Retain the subordinate parent through allocation + full sample budget.
        # Only the harness releases it after validating the native row; the
        # independent 20-second alarm still bounds a lost harness/owner.
        while not (directory / "release").exists():
            time.sleep(0.02)
        return
    if kind == "root-exit":
        time.sleep(0.2)
        os._exit(7)
    if kind in ("timeout", "rss", "term", "controller-loss"):
        time.sleep(10)
    else:
        time.sleep(1.0 if kind == "nested" else 0.4)


def receipt(path):
    return dict(line.split("=", 1) for line in path.read_text().splitlines())


def absent(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return True
    return False


def nested_guard_mode():
    # The coordinator wraps this harness in the same candidate reaper guard.
    # Nested guards must retain its admitted session contract.
    return ["--session-mode=inherit"] if "SIMPLE_BOOTSTRAP_SESSION_ID" in os.environ else []


def run_guard_case(guard, root, kind, expected, sentinel):
    case = root / kind
    case.mkdir()
    output = case / "receipt.env"
    command = ["perl", str(guard), *nested_guard_mode(), f"--receipt={output}", "--interval-ms=100",
               "--max-rss-kib=" + ("65536" if kind == "rss" else "1048576" if kind in ("twenty", "fork-race") else "262144"),
               "--timeout-seconds=" + ("1" if kind in ("timeout", "fork-race") else "15"),
               "--", sys.executable, str(Path(__file__).resolve()), "--fixture", kind,
               "--output", str(case)]
    start = time.monotonic()
    with (case / "stdout").open("wb") as out, (case / "stderr").open("wb") as err:
        proc = subprocess.Popen(command, stdout=out, stderr=err)
        try:
            if kind == "term":
                until = time.monotonic() + 10
                while not (case / "ready").exists() and proc.poll() is None and time.monotonic() < until:
                    time.sleep(0.02)
                assert (case / "ready").exists(), "TERM fixture never started"
                proc.terminate()
            status = proc.wait(timeout=25)
        except BaseException:
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()  # owner observes parent death; no descendant PID guessing
                proc.wait(timeout=3)
            raise
    result = receipt(output)
    assert status == expected, (kind, status, expected, result)
    assert result["containment_scope"] == "freebsd-reaper-descendants"
    assert result["quiescent"] == ("0" if kind == "kill-owner" else "1"), result
    assert result["rss_cap_enforced"] == "1"
    assert sentinel.poll() is None, "unrelated sentinel was killed"
    if kind != "kill-owner":
        pids = [int(p) for p in (case / "pids").read_text().splitlines()]
        assert all(absent(pid) for pid in pids), (kind, "surviving fixture PID", pids)
    if kind in ("pty", "twenty", "nested"):
        assert int(result["cross_session_owned_peak"]) > 0, result
    if kind == "nested":
        assert int(result["peak_rss_kib"]) >= 32 * 1024, "nested allocation absent from total RSS"
    assert float(result["sample_duration_max_ms"]) <= float(result["observation_budget_ms"])
    return {"case": kind, "status": "PASS", "elapsed_s": time.monotonic() - start,
            "receipt": str(output), "guard_exit": status}


def direct_owner_case(helper, root, mode):
    """Channel failure must clean children even without a functioning Perl peer."""
    directory = root / mode
    directory.mkdir()
    req_read, req_write = os.pipe()
    reply_read, reply_write = os.pipe()
    command = [str(helper), "--reaper-owner", str(req_read), str(reply_write), "5000", "--",
               sys.executable, str(Path(__file__).resolve()), "--fixture", "controller-loss",
               "--output", str(directory)]
    with (directory / "owner.log").open("wb") as log:
        proc = subprocess.Popen(command, pass_fds=(req_read, reply_write), stderr=log,
                                stdout=log)
        os.close(req_read)
        os.close(reply_write)
        try:
            os.write(req_write, b"G")
            until = time.monotonic() + 5
            while not (directory / "ready").exists() and time.monotonic() < until:
                if proc.poll() is not None:
                    break
                time.sleep(0.02)
            assert (directory / "ready").exists(), "direct owner never released fixture"
            if mode == "malformed-command":
                os.write(req_write, b"?")
            os.close(req_write)
            req_write = -1
            assert proc.wait(timeout=5) == 89
            pids = [int(p) for p in (directory / "pids").read_text().splitlines()]
            assert all(absent(pid) for pid in pids), "channel-loss left descendants"
        finally:
            if req_write >= 0:
                os.close(req_write)
            os.close(reply_read)
            if proc.poll() is None:
                proc.terminate()
                proc.wait(timeout=5)
    return {"case": mode, "status": "PASS"}


def parent_death_case(helper, root):
    directory = root / "parent-death"
    directory.mkdir()
    req_read, req_write = os.pipe()
    reply_read, reply_write = os.pipe()
    command = [sys.executable, str(Path(__file__).resolve()), "--output", str(directory),
               "--owner-parent", str(helper), str(req_read), str(reply_write)]
    with (directory / "owner.log").open("wb") as log:
        parent = subprocess.Popen(command, pass_fds=(req_read, reply_write), stdout=log, stderr=log)
        os.close(req_read)
        os.close(reply_write)
        try:
            os.write(req_write, b"G")
            until = time.monotonic() + 5
            while not (directory / "ready").exists() and time.monotonic() < until:
                time.sleep(0.02)
            assert (directory / "ready").exists()
            parent.kill()
            parent.wait(timeout=2)
            # Keep request pipe open: cleanup must come from PDEATHSIG, not EOF.
            pids = [int(p) for p in (directory / "pids").read_text().splitlines()]
            owner = int((directory / "owner-pid").read_text())
            until = time.monotonic() + 4
            while not all(absent(pid) for pid in [owner, *pids]) and time.monotonic() < until:
                time.sleep(0.02)
            assert all(absent(pid) for pid in [owner, *pids]), "parent death did not clean hierarchy"
        finally:
            os.close(req_write)
            os.close(reply_read)
            if parent.poll() is None:
                parent.terminate()
                parent.wait(timeout=5)
    return {"case": "parent-death", "status": "PASS"}


def nested_rss_case(helper, root):
    directory = root / "nested-rss-membership"
    directory.mkdir()
    req_read, req_write = os.pipe()
    reply_read, reply_write = os.pipe()
    command = [str(helper), "--reaper-owner", str(req_read), str(reply_write), "5000", "--",
               sys.executable, str(Path(__file__).resolve()), "--fixture", "nested-held", "--output", str(directory)]

    def response(ending):
        data = b""
        until = time.monotonic() + 5
        while not data.endswith(ending):
            remaining = until - time.monotonic()
            assert remaining > 0 and select.select([reply_read], [], [], remaining)[0], "owner reply timeout"
            part = os.read(reply_read, 4096)
            assert part and len(data) + len(part) <= 3 * 1024 * 1024, "invalid owner reply size/EOF"
            data += part
        return data.decode("ascii")

    with (directory / "owner.log").open("wb") as log:
        owner = subprocess.Popen(command, pass_fds=(req_read, reply_write), stdout=log, stderr=log)
        os.close(req_read)
        os.close(reply_write)
        try:
            os.write(req_write, b"G")
            until = time.monotonic() + 5
            while not (directory / "allocated.json").exists() and time.monotonic() < until:
                time.sleep(0.01)
            allocated = json.loads((directory / "allocated.json").read_text())
            os.write(req_write, b"S")
            sample = response(b"END\n")
            (directory / "native-sample.txt").write_text(sample)
            lines = sample.splitlines()
            header = lines[0].split()
            assert header[:2] == ["SAMPLE", "1"] and int(header[2]) == owner.pid
            assert len(lines[1:-1]) == int(header[5])
            rows = {int(row[0]): [int(value) for value in row] for row in (line.split() for line in lines[1:-1])}
            row = rows[allocated["pid"]]
            assert row[1] == int(header[3]), "RSS fixture is not child of subordinate reaper"
            assert row[3] == row[0] and row[4] >= allocated["minimum_rss_kib"] and row[5] == 0
            (directory / "release").touch()
            os.write(req_write, b"Q")
            clean = response(b"\n")
            assert clean.startswith("QUIET 1 ") and owner.wait(timeout=3) == 0
            assert absent(allocated["pid"])
        finally:
            os.close(req_write)
            os.close(reply_read)
            if owner.poll() is None:
                owner.terminate()
                owner.wait(timeout=5)
    return {"case": "nested-rss-membership", "status": "PASS", "observed_pid": allocated["pid"],
            "observed_rss_kib": row[4], "native_sample": str(directory / "native-sample.txt")}


def zombie_reaper_case(helper, library, root, held, sentinel):
    """Real zombie ownership; the interposer only schedules its observation."""
    kind = "zombie-held" if held else "zombie-waitable"
    directory = root / kind
    directory.mkdir()
    marker = directory / "barrier"
    req_read, req_write = os.pipe()
    reply_read, reply_write = os.pipe()
    env = dict(os.environ, LD_PRELOAD=str(library.resolve()),
               SIMPLE_REAPER_FAULT_MARKER=str(marker.resolve()), SIMPLE_REAPER_FAULT_MODE="zombie-barrier")
    command = [str(helper), "--reaper-owner", str(req_read), str(reply_write), "5000", "--",
               sys.executable, str(Path(__file__).resolve()), "--fixture", kind, "--output", str(directory)]

    def wait_file(path):
        until = time.monotonic() + 5
        while not path.exists():
            assert owner.poll() is None and time.monotonic() < until, "zombie barrier deadline"
            time.sleep(0.001)

    def line(deadline):
        data = b""
        while not data.endswith(b"\n"):
            left = deadline - time.monotonic()
            assert left > 0 and select.select([reply_read], [], [], left)[0], "zombie reply deadline"
            part = os.read(reply_read, 1)
            assert part and len(data) < 256, "zombie reply EOF/size"
            data += part
        return data.decode("ascii")

    def sample():
        deadline = time.monotonic() + 5
        header = line(deadline)
        fields = header.split()
        assert len(fields) == 6 and fields[:2] == ["SAMPLE", "1"] and int(fields[2]) == owner.pid, header
        count = int(fields[5])
        assert 1 <= count <= 16385
        body = [line(deadline) for _ in range(count)]
        assert line(deadline) == "END\n"
        rows = {}
        for text in body:
            row = [int(value) for value in text.split()]
            assert len(row) == 8 and row[0] not in rows
            rows[row[0]] = row
        return fields, rows, header + "".join(body) + "END\n"

    with (directory / "owner.log").open("wb") as log:
        owner = subprocess.Popen(command, pass_fds=(req_read, reply_write), stdout=log, stderr=log, env=env)
        os.close(req_read)
        os.close(reply_write)
        try:
            os.write(req_write, b"G")
            wait_file(directory / "allocated.json")
            allocated = json.loads((directory / "allocated.json").read_text())
            os.write(req_write, b"S")
            initial_header, initial, initial_text = sample()
            (directory / "before.txt").write_text(initial_text)
            leaf = initial[allocated["pid"]]
            target = initial[leaf[1]]
            assert leaf[4] >= allocated["minimum_rss_kib"] and leaf[5] == target[5] == 0
            assert (target[0] == int(initial_header[3])) != held
            marker.write_text(f"{target[0]} {target[6]} {target[7]} {leaf[0]} {leaf[6]} {leaf[7]}\n")
            os.write(req_write, b"S")
            wait_file(directory / "barrier.entered")
            (directory / "exit-reaper").touch()
            if held:
                deadline = time.monotonic() + 5
                failure = line(deadline)
                fields = failure.split()
                assert fields == ["ERROR", "1", str(owner.pid), "sample", "owner-zombie-unreaped",
                                  str(target[0]), "0", "3", "0", "-1", "-1"], failure
                stopped = line(deadline)
                stop = stopped.split()
                assert len(stop) == 11 and stop[:5] == ["ERROR", "1", str(owner.pid), "stop", "sample-failed"]
                assert stop[5:10] == [str(os.getpid()), "0", "0", "0", "1"] and int(stop[10]) >= 0
                assert owner.wait(timeout=3) == 89
                (directory / "terminal-errors.txt").write_text(failure + stopped)
                result = {"expected_sample_failure": True, "cleanup_quiet": 1, "owner_exit": 89}
            else:
                header, rows, text = sample()
                (directory / "after.txt").write_text(text)
                retained = rows[leaf[0]]
                assert retained[6:] == leaf[6:] and retained[5] == 0 and retained[4] >= allocated["minimum_rss_kib"]
                assert retained[1] == owner.pid and target[0] not in rows
                assert int(header[4]) == 7 << 8, "wait drain lost payload exit status"
                os.write(req_write, b"Q")
                quiet = line(time.monotonic() + 4)
                fields = quiet.split()
                assert fields == ["QUIET", "1", str(7 << 8), str(owner.pid),
                                  str(initial[owner.pid][6]), str(initial[owner.pid][7])], quiet
                assert owner.wait(timeout=3) == 0
                (directory / "quiet.txt").write_text(quiet)
                result = {"observed_rss_kib": retained[4], "cleanup_quiet": 1, "owner_exit": 0}
            observed = [int(value) for value in (directory / "barrier.observed").read_text().split()]
            assert observed[:6] == [target[0], target[6], target[7], leaf[0], leaf[6], leaf[7]]
            assert len(observed) == 8 and observed[6] >= allocated["minimum_rss_kib"] and observed[7] == target[0]
            # QUIET proves the entire hierarchy absent; PID checks only supplement it.
            assert all(absent(pid) for pid in initial) and sentinel.poll() is None
            result.update(case=kind, status="PASS", native_owner=owner.pid,
                          nested_identity=target[6:], leaf_identity=leaf[6:])
            (directory / "result.json").write_text(json.dumps(result, indent=2) + "\n")
            return result
        finally:
            marker.unlink(missing_ok=True)
            os.close(req_write)
            os.close(reply_read)
            if owner.poll() is None:
                owner.terminate()
                owner.wait(timeout=8)


def native_fault_case(helper, library, root, mode):
    directory = root / mode
    directory.mkdir()
    marker = directory / "inject"
    req_read, req_write = os.pipe()
    reply_read, reply_write = os.pipe()

    def reply_line(deadline):
        data = b""
        while len(data) < 256:
            remaining = deadline - time.monotonic()
            assert remaining > 0 and select.select([reply_read], [], [], remaining)[0], "fault reply deadline"
            byte = os.read(reply_read, 1)
            if not byte:
                assert not data, "truncated fault reply"
                return b""
            data += byte
            if byte == b"\n":
                return data
        raise AssertionError("oversized fault reply")

    def terminal_errors(owner_pid):
        deadline = time.monotonic() + 1
        seen = set()
        records = []
        while True:
            line = reply_line(deadline)
            if not line:
                break
            assert len(records) < 2, "too many terminal fault records"
            match = re.fullmatch(rb"ERROR 1 ([1-9][0-9]*) (sample|stop) ([a-z-]+) ([1-9][0-9]*) ([0-9]+) ([0-9]+) ([0-9]+) (-1|[01]) (-1|[0-9]+)\n", line)
            assert match, "fault emitted a successful sample or malformed terminal record"
            record_owner, phase, stage, pid, error, attempts, sig, quiet, raw = match.groups()
            assert int(record_owner) == owner_pid and phase not in seen, "fault diagnostic owner/phase mismatch"
            assert int(sig) == 0 and -1 <= int(raw) <= 65535, "invalid fault diagnostic signal/status"
            if phase == b"sample":
                expected = {"query-denied": (b"list-query", errno.EPERM), "query-full": (b"list-saturated", 0)}
                assert mode in expected and (stage, int(error)) == expected[mode], "unexpected query failure stage"
                assert int(pid) == owner_pid and 1 <= int(attempts) <= 3 and int(quiet) == -1
            else:
                expected = (b"cleanup-requested", 0) if mode == "cleanup-denied" else (b"sample-failed", 1)
                assert (stage, int(quiet)) == expected and int(pid) == os.getpid(), "unexpected terminal cleanup stage"
                assert int(error) == 0 and int(attempts) == 0
            seen.add(phase)
            records.append(line)
        # Diagnostics are best effort; EOF alone remains valid after the actual
        # native exit and descendant-cleanup assertions, never a successful sample.
        (directory / "terminal-errors.txt").write_bytes(b"".join(records))

    env = dict(os.environ, LD_PRELOAD=str(library.resolve()),
               SIMPLE_REAPER_FAULT_MARKER=str(marker.resolve()), SIMPLE_REAPER_FAULT_MODE=mode)
    command = [str(helper), "--reaper-owner", str(req_read), str(reply_write), "5000", "--",
               sys.executable, str(Path(__file__).resolve()), "--fixture", "controller-loss", "--output", str(directory)]
    with (directory / "owner.log").open("wb") as log:
        owner = subprocess.Popen(command, pass_fds=(req_read, reply_write), stdout=log, stderr=log, env=env)
        os.close(req_read)
        os.close(reply_write)
        try:
            os.write(req_write, b"G")
            until = time.monotonic() + 5
            while not (directory / "ready").exists() and time.monotonic() < until:
                time.sleep(0.01)
            assert (directory / "ready").exists(), "fault fixture did not start"
            pids = [int(p) for p in (directory / "pids").read_text().splitlines()]
            marker.touch()
            if mode == "cleanup-denied":
                os.write(req_write, b"Q")
                data = reply_line(time.monotonic() + 4)
                fields = data.decode("ascii").split()
                assert len(fields) == 6 and fields[:2] == ["QUIET", "0"] and int(fields[3]) == owner.pid
                assert int(fields[4]) > 0 and 0 <= int(fields[5]) < 1000000
                (directory / "retained-owner.txt").write_bytes(data)
                time.sleep(1)
                assert owner.poll() is None and all(not absent(pid) for pid in pids), "failed cleanup lost ownership"
                marker.unlink()
                assert owner.wait(timeout=8) == 0, "owner failed to clean after permission fault was removed"
            else:
                os.write(req_write, b"S")
                assert owner.wait(timeout=5) == 89, "incomplete kernel query was accepted"
            terminal_errors(owner.pid)
            assert all(absent(pid) for pid in pids), "native fault left descendants after cleanup"
        finally:
            marker.unlink(missing_ok=True)
            os.close(req_write)
            os.close(reply_read)
            if owner.poll() is None:
                owner.terminate()
                owner.wait(timeout=8)
    return {"case": mode, "status": "PASS", "fault_library_sha256": hashlib.sha256(library.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--fixture")
    parser.add_argument("--owner-parent", nargs=3)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--original-command", nargs=argparse.REMAINDER)
    parser.add_argument("--original-spec", type=Path)
    parser.add_argument("--original-spec-sha256")
    parser.add_argument("--original-seed-sha256")
    parser.add_argument("--original-expected-examples", type=int)
    parser.add_argument("--fault-library", type=Path)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--continuation-helper", type=Path,
                       help="run wait-drain regression and unfinished cases with this frozen helper")
    modes.add_argument("--zombie-negative-helper", type=Path,
                       help="only the deliberate unobservable-branch case; separate guarded job required")
    modes.add_argument("--remaining-helper", type=Path, help="run only unfinished ownership/fault cases and original pane")
    args = parser.parse_args()
    if args.owner_parent:
        helper, read_fd, write_fd = args.owner_parent
        signal.alarm(12)
        child = subprocess.Popen([helper, "--reaper-owner", read_fd, write_fd, "5000", "--",
            sys.executable, str(Path(__file__).resolve()), "--fixture", "controller-loss",
            "--output", str(args.output)], pass_fds=(int(read_fd), int(write_fd)))
        (args.output / "owner-pid").write_text(str(child.pid))
        return child.wait(timeout=10)
    if args.fixture:
        fixture(args.fixture, args.output)
        return 0
    if not sys.platform.startswith("freebsd"):
        parser.error("FreeBSD runtime gate; unsupported host is not a PASS")
    if (args.continuation_helper or args.zombie_negative_helper or args.remaining_helper) and not args.fault_library:
        parser.error("focused zombie cases require the frozen --fault-library")
    args.output.mkdir(parents=True, exist_ok=False)
    guard = Path(__file__).resolve().with_name("process-tree-rss-watchdog.pl")
    results = []
    sentinel = subprocess.Popen(["/bin/sleep", "300"])
    try:
        if args.zombie_negative_helper:
            results.append(zombie_reaper_case(args.zombie_negative_helper.resolve(),
                args.fault_library, args.output, True, sentinel))
            return 0
        cases = (("pty", 0), ("double-fork", 0), ("root-exit", 7),
                 ("nested", 0), ("twenty", 0), ("rss", 88),
                 ("timeout", 124), ("term", 143), ("fork-race", 124), ("kill-owner", 89))
        if args.continuation_helper:
            helper = args.continuation_helper.resolve()
            results.append(zombie_reaper_case(helper, args.fault_library, args.output, False, sentinel))
            cases = (("fork-race", 124), ("kill-owner", 89))
        if args.remaining_helper:
            helper = args.remaining_helper.resolve()
            cases = ()
        for case, expected in cases:
            results.append(run_guard_case(guard, args.output, case, expected, sentinel))
        if not (args.continuation_helper or args.remaining_helper):
            helper = Path(receipt(args.output / "pty" / "receipt.env")["session_helper"])
            if args.fault_library:
                results.append(zombie_reaper_case(helper, args.fault_library, args.output, False, sentinel))
        for mode in ("control-eof", "malformed-command"):
            results.append(direct_owner_case(helper, args.output, mode))
        results.append(parent_death_case(helper, args.output))
        results.append(nested_rss_case(helper, args.output))
        if args.fault_library:
            for mode in ("cleanup-denied", "query-denied", "query-full"):
                results.append(native_fault_case(helper, args.fault_library, args.output, mode))
        else:
            results.append({"case": "native-fault-injection", "status": "NOT_RUN"})
        if args.original_command:
            expected = args.original_expected_examples
            assert expected and expected > 0 and args.original_spec, "original spec admission missing"
            original_spec = args.original_spec.resolve()
            assert original_spec.as_posix().endswith("/test/01_unit/app/llm_caret/pane_backend_spec.spl")
            assert str(original_spec) in args.original_command, "command does not run the exact original spec"
            spec_bytes = original_spec.read_bytes()
            assert hashlib.sha256(spec_bytes).hexdigest() == args.original_spec_sha256
            assert len(re.findall(rb'^\s*it\s+"', spec_bytes, re.MULTILINE)) == expected
            seed = Path(args.original_command[0]).resolve()
            assert hashlib.sha256(seed.read_bytes()).hexdigest() == args.original_seed_sha256
            path = args.output / "original-pane"
            path.mkdir()
            with (path / "output.log").open("wb") as log:
                run = subprocess.run(["perl", str(guard), *nested_guard_mode(), f"--receipt={path / 'receipt.env'}",
                    "--timeout-seconds=150", "--", *args.original_command], stdout=log,
                    stderr=subprocess.STDOUT, timeout=160)
            evidence = receipt(path / "receipt.env")
            assert run.returncode == 0 and evidence["quiescent"] == "1", evidence
            text = (path / "output.log").read_text(errors="replace")
            text = re.sub(r"\x1b\[[0-9;]*m", "", text)
            summaries = re.findall(r"^Results: (\d+) total, (\d+) passed, (\d+) failed"
                r"(?:, (\d+) skipped)?(?:, (\d+) dropped)?\s*$", text, re.MULTILINE)
            assert len(summaries) == 1, "missing/ambiguous canonical original-spec result"
            total, passed, failed, skipped, dropped = (int(value or 0) for value in summaries[0])
            assert (total, passed, failed, skipped, dropped) == (expected, expected, 0, 0, 0)
            prefix = f"SPEC FILE VERDICT: {original_spec} "
            verdicts = [line[len(prefix):] for line in text.splitlines() if line.startswith(prefix)]
            assert len(verdicts) == 1, "missing/ambiguous original-spec execution verdict"
            tokens = verdicts[0].split()
            assert all(token.count("=") == 1 for token in tokens), "malformed execution verdict"
            verdict = dict(token.split("=", 1) for token in tokens)
            assert len(verdict) == len(tokens), "duplicate execution verdict fields"
            assert set(verdict) == {"outcome", "declared>", "executed", "passed", "failed", "skipped", "dropped"}
            assert verdict["outcome"] == "OK" and verdict["declared>"].isdigit()
            counters = ("executed", "passed", "failed", "skipped", "dropped")
            assert all(verdict[key].isdigit() for key in counters), "invalid execution verdict counters"
            observed = tuple(int(verdict[key]) for key in counters)
            assert observed == (expected, expected, 0, 0, 0), "original spec did not execute every admitted example"
            assert hashlib.sha256(original_spec.read_bytes()).hexdigest() == args.original_spec_sha256
            assert hashlib.sha256(seed.read_bytes()).hexdigest() == args.original_seed_sha256
            results.append({"case": "original-pane", "status": "PASS", "executed": observed[0],
                            "passed": passed, "failed": failed, "skipped": skipped, "dropped": dropped,
                            "spec_sha256": args.original_spec_sha256, "seed_sha256": args.original_seed_sha256})
        else:
            results.append({"case": "original-pane", "status": "NOT_RUN"})
    except BaseException as error:
        results.append({"status": "FAIL", "error": repr(error)})
    finally:
        sentinel.terminate()
        sentinel.wait(timeout=3)
        (args.output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    return 0 if results and all(item["status"] == "PASS" for item in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
