#!/usr/bin/env python3
"""Exercise the real claim writer with a bounded reseal barrier and private DB."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


def wait_until(predicate, label, timeout=90):
    deadline = time.monotonic() + timeout
    while not predicate():
        if time.monotonic() >= deadline:
            raise AssertionError("timeout: " + label)
        time.sleep(0.05)


class Fixture:
    def __init__(self, root, source, shell):
        self.root, self.shell = root, shell
        self.db = root / "bug_db.sdn"
        self.lock = Path(str(self.db) + ".lock")
        self.processes = []
        self.logs = {}
        root.mkdir()
        shutil.copyfile(source, root / "bug-claim.shs")
        self.db.write_text(
            "#sdn-crc32:0\n"
            "bugs |id, severity, status, title, file, line, reproducible_by, created_at, updated_at, valid|\n"
            '    A, P2, open, "a", a.spl, 1, NONE, 2026-11-03, 2026-11-03, true\n'
            '    B, P2, open, "b", b.spl, 1, NONE, 2026-11-03, 2026-11-03, true\n'
            "bug_fix_claims |bug_id, state, session_id, claimed_at, heartbeat_at, prev_status, note|\n",
            encoding="utf-8",
        )
        # Only checksum work is replaced. Locking, snapshotting, edits, publish,
        # claimant output and cleanup all execute the real production helper.
        (root / "reseal-sdn-crc32.shs").write_text(
            '#!/bin/sh\nif [ "${CLAIM_FIXTURE_HOLD:-}" = 1 ]; then\n'
            '  touch "$CLAIM_FIXTURE_READY"\n'
            '  i=0; while [ ! -f "$CLAIM_FIXTURE_RELEASE" ]; do\n'
            '    i=$((i+1)); [ "$i" -lt 600 ] || exit 91; sleep 0.1\n'
            '  done\nfi\nexit 0\n', encoding="utf-8"
        )

    def start(self, bug, hold=False):
        env = dict(os.environ, BUG_CLAIM_DB=self.db.as_posix(),
                   BUG_CLAIM_NOW="2026-11-03T00:00:00Z",
                   CLAIM_FIXTURE_HOLD="1" if hold else "0",
                   CLAIM_FIXTURE_READY=(self.root / "ready").as_posix(),
                   CLAIM_FIXTURE_RELEASE=(self.root / "release").as_posix())
        # Git sh launched from PowerShell otherwise finds Windows FIND.EXE
        # ahead of POSIX find, silently disabling the original age-steal path.
        env["PATH"] = str(Path(self.shell).resolve().parent) + os.pathsep + env.get("PATH", "")
        log_path = self.root / ("trace-" + bug + ".log")
        log = log_path.open("w", encoding="utf-8")
        process = subprocess.Popen(
            [self.shell, "-x", (self.root / "bug-claim.shs").as_posix(), "claim", bug, "session-" + bug],
            env=env, stdout=log, stderr=subprocess.STDOUT,
            text=True, creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
        )
        log.close()
        self.processes.append(process)
        self.logs[process] = log_path
        return process

    def held(self):
        process = self.start("A", hold=True)
        wait_until(lambda: (self.root / "ready").exists() or process.poll() is not None,
                   "first claimant reached reseal")
        assert process.poll() is None, self.logs[process].read_text(encoding="utf-8")
        owners = list(self.lock.glob("owner.*"))
        assert len(owners) <= 1, "multiple owner markers"
        # The old helper has no marker; permit that only so its age-stealing
        # behavior can be exercised as a negative control for the first case.
        return process, owners[0] if owners else None

    def finish(self, process, success=True):
        process.wait(timeout=60)
        output = self.logs[process].read_text(encoding="utf-8")
        assert (process.returncode == 0) == success, output
        return output

    def close(self):
        (self.root / "release").touch()
        for process in self.processes:
            if process.poll() is None:
                try:
                    process.communicate(timeout=12)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.communicate(timeout=5)


def live_old_owner(fixture):
    first, owner = fixture.held()
    # Make the actual directory older than the former two-minute stealing rule
    # without sleeping for two minutes. The owner remains demonstrably alive.
    old = time.time() - 600
    os.utime(fixture.lock, (old, old))
    second = fixture.start("B")
    # Observe a completed contention attempt rather than assuming shell startup
    # has reached mkdir after a short sleep (not reliable on loaded Windows).
    wait_until(lambda: "+ sleep 1" in fixture.logs[second].read_text(encoding="utf-8")
               or len(list(fixture.root.glob("bug_db.sdn.work.*"))) > 1
               or second.poll() is not None, "second claimant attempted the held lock")
    assert first.poll() is None and second.poll() is None, "live old lock was stolen"
    assert len(list(fixture.root.glob("bug_db.sdn.work.*"))) == 1, "contender copied DB under a live lock"
    if owner is not None:
        assert owner.exists(), "live owner's token changed"
    (fixture.root / "release").touch()
    assert "CLAIMED: A" in fixture.finish(first)
    assert "CLAIMED: B" in fixture.finish(second)
    body = fixture.db.read_text(encoding="utf-8")
    assert "A, fixing, session-A" in body and "B, fixing, session-B" in body
    assert not fixture.lock.exists(), "completed owners leaked lock"


def recover_dead_owner(fixture):
    fixture.lock.mkdir()
    # Obtain a real PID from this shell namespace, then wait for its owner to
    # exit. Do not confuse Windows native subprocess PIDs with MSYS shell $$.
    dead = subprocess.check_output([fixture.shell, "-c", "echo $$"], text=True).strip()
    marker = fixture.lock / ("owner." + dead + ".dead-fixture")
    marker.touch()
    process = fixture.start("B")
    assert "CLAIMED: B" in fixture.finish(process)
    assert "B, fixing, session-B" in fixture.db.read_text(encoding="utf-8")
    assert not fixture.lock.exists(), "dead owner's lock was not recovered"


def replacement_survives_cleanup(fixture):
    first, owner = fixture.held()
    assert owner is not None, "missing unique owner marker"
    # Simulate an external replacement while the first writer is paused. Its
    # commit must fail closed; its exit cleanup must preserve the replacement.
    owner.unlink()
    fixture.lock.rmdir()
    fixture.lock.mkdir()
    replacement = fixture.lock / "owner.1.replacement-fixture"
    replacement.touch()
    (fixture.root / "release").touch()
    output = fixture.finish(first, success=False)
    assert "lost lock ownership" in output, output
    assert replacement.exists(), "old cleanup removed the replacement owner"
    assert "A, fixing, session-A" not in fixture.db.read_text(encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shell", default=shutil.which("sh"))
    parser.add_argument("--script", type=Path, default=Path(__file__).with_name("bug-claim.shs"))
    scenarios = (live_old_owner, recover_dead_owner, replacement_survives_cleanup)
    parser.add_argument("--scenario", choices=[scenario.__name__ for scenario in scenarios])
    args = parser.parse_args()
    if not args.shell:
        parser.error("a POSIX shell is required; pass --shell")
    with tempfile.TemporaryDirectory(prefix="bug-claim-lock-") as directory:
        selected = [scenario for scenario in scenarios if not args.scenario or scenario.__name__ == args.scenario]
        for scenario in selected:
            fixture = Fixture(Path(directory) / scenario.__name__, args.script.resolve(), args.shell)
            try:
                scenario(fixture)
                print("PASS " + scenario.__name__, flush=True)
            finally:
                fixture.close()
    print("STATUS: PASS bug-claim owner locking (" + str(len(selected)) + " scenarios)")


if __name__ == "__main__":
    main()
