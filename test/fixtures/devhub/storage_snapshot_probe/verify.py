"""Native snapshot acceptance. Pass an already built isolated probe executable.

No compiler rebuild/build is launched. Private 4096-byte SQLite fixtures use real
sqlite3 locks; any missing symlink capability fails explicitly rather than skips.
Run after the earlier encrypted-read acceptance, under the global native queue.
"""
from __future__ import annotations
import argparse
import hashlib
import os
from pathlib import Path
import shutil
import sqlite3
import subprocess
import tempfile
import time


def environment(path: Path, mode: str, ready: Path | None = None) -> dict[str, str]:
    result = os.environ.copy()
    result.update(DEVHUB_SNAPSHOT_PATH=str(path), DEVHUB_SNAPSHOT_MODE=mode)
    if ready is not None:
        result['DEVHUB_SNAPSHOT_READY'] = str(ready)
    return result


def run(probe: Path, path: Path, mode: str) -> None:
    completed = subprocess.run([str(probe)], env=environment(path, mode),
                               capture_output=True, text=True, timeout=15)
    assert completed.returncode == 0, (mode, path.name, completed.stdout, completed.stderr)
    assert 'PASS ' in completed.stdout, ('zero assertion output', completed.stdout)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--probe', type=Path, required=True)
    args = parser.parse_args()
    probe = args.probe.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix='devhub-snapshot-') as temporary:
        directory = Path(temporary)
        base = directory / 'rollback.sqlite'
        with sqlite3.connect(base) as database:
            database.execute('PRAGMA page_size=4096')
            assert database.execute('PRAGMA journal_mode=DELETE').fetchone() == ('delete',)
            database.execute('CREATE TABLE messages(id INTEGER PRIMARY KEY, body TEXT)')
            database.executemany('INSERT INTO messages(body) VALUES(?)', [('x' * 500,) for _ in range(24)])
            database.commit()
            assert database.execute('PRAGMA integrity_check').fetchone() == ('ok',)
        digest = hashlib.sha256(base.read_bytes()).hexdigest()
        run(probe, base, 'read')
        assert hashlib.sha256(base.read_bytes()).hexdigest() == digest
        for suffix in ('-journal', '-wal', '-shm'):
            sidecar = Path(str(base) + suffix)
            sidecar.write_bytes(b'')
            run(probe, base, 'refuse')
            sidecar.unlink()
        link = directory / 'symlink.sqlite'
        # Permission errors on Windows must be resolved before qualification.
        link.symlink_to(base)
        run(probe, link, 'refuse')
        link.unlink()
        hard = directory / 'hardlink.sqlite'
        os.link(base, hard)
        run(probe, hard, 'refuse')
        run(probe, base, 'refuse')
        hard.unlink()
        with sqlite3.connect(base, timeout=0) as writer:
            writer.execute('BEGIN EXCLUSIVE')
            run(probe, base, 'refuse')
            writer.rollback()
        run(probe, base, 'read')
        altered = directory / 'wal-header.sqlite'
        image = bytearray(base.read_bytes())
        image[18:20] = b'\x02\x02'
        altered.write_bytes(image)
        run(probe, altered, 'header-refuse')
        wal = directory / 'active-wal.sqlite'
        shutil.copyfile(base, wal)
        with sqlite3.connect(wal) as writer:
            assert writer.execute('PRAGMA journal_mode=WAL').fetchone() == ('wal',)
            writer.execute("INSERT INTO messages(body) VALUES('wal committed')")
            writer.commit()
            run(probe, wal, 'refuse')
        # Reverse contention: a real native owner must block SQLite COMMIT,
        # while allowing another existing connection to hold RESERVED.
        ready = directory / 'ready'
        child = subprocess.Popen([str(probe)], env=environment(base, 'hold', ready),
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 10
            while not ready.exists():
                assert child.poll() is None, 'native owner exited before readiness'
                assert time.monotonic() < deadline, 'native lock readiness timed out'
                time.sleep(0.02)
            writer = sqlite3.connect(base, timeout=0)
            try:
                writer.execute('BEGIN IMMEDIATE')
                writer.execute("INSERT INTO messages(body) VALUES('after native read')")
                try:
                    writer.commit()
                except sqlite3.OperationalError as error:
                    assert 'locked' in str(error).lower(), str(error)
                else:
                    raise AssertionError('SQLite commit passed through native shared lock')
                writer.rollback()
            finally:
                writer.close()
            stdout, stderr = child.communicate(timeout=10)
            assert child.returncode == 0 and 'PASS ' in stdout, (stdout, stderr)
        finally:
            if child.poll() is None:
                child.kill()
                child.communicate()
        with sqlite3.connect(base, timeout=0) as writer:
            writer.execute("INSERT INTO messages(body) VALUES('commit after release')")
            writer.commit()
        run(probe, base, 'read')
        print('PASS native snapshot: exact reads, lifecycle, symlink/hardlink, sidecars, WAL and bidirectional SQLite contention')


if __name__ == '__main__':
    main()
