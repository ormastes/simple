#!/usr/bin/env python3
"""Exit 0 only for an unchanged, out-of-scope HEAD leaf behind a tracked alias.

This is a conservative duplicate classifier, not a receipt consumer. Any missing
tool, malformed identity, filter, changed byte or ambiguous mapping means scan.
Only exact committed bytes are accepted (no clean-filter or EOL normalization).
"""
import os
from pathlib import Path, PurePosixPath
import stat
import subprocess
import sys
import threading
import time

MAX_SOURCE_BYTES = 1024 * 1024
MAX_ALIAS_BYTES = 4096
MAX_METADATA_BYTES = 64 * 1024
WALL_SECONDS = 5.0
REAP_SECONDS = 1.0


class Budget:
    """One request owns its deadline, cancellation and sole Git child."""
    def __init__(self):
        self.deadline = time.monotonic() + WALL_SECONDS
        self.cancelled = threading.Event()
        self.lock = threading.Lock()
        self.child = None

    def check(self):
        if self.cancelled.is_set() or time.monotonic() >= self.deadline:
            raise TimeoutError("classifier wall budget")

    def cancel(self):
        # The lock covers spawn registration only, never reads or waits.
        with self.lock:
            self.cancelled.set()
            child = self.child
        if child is not None:
            if child.poll() is None:
                child.kill()
            child.wait(timeout=REAP_SECONDS)

    def git(self, root, args, limit):
        env = os.environ.copy()
        env.update(GIT_NO_LAZY_FETCH="1", GIT_TERMINAL_PROMPT="0",
                   GIT_OPTIONAL_LOCKS="0")
        # No pager, filesystem-monitor hook or promisor fetch subprocess can
        # escape the single owned plumbing process. Old Git rejects the flag.
        command = ["git", "--no-pager", "--no-lazy-fetch", "--literal-pathspecs",
                   "-c", "core.fsmonitor=false", *args]
        with self.lock:
            self.check()
            child = subprocess.Popen(command, cwd=root, env=env,
                                     stdin=subprocess.DEVNULL,
                                     stdout=subprocess.PIPE,
                                     stderr=subprocess.DEVNULL)
            self.child = child
        try:
            data = child.stdout.read(limit + 1)
            self.check()
            if len(data) > limit:
                raise ValueError("Git output ceiling")
            if child.wait(timeout=max(0.001, self.deadline - time.monotonic())):
                raise ValueError("Git plumbing failed")
            return data
        finally:
            if child.poll() is None:
                child.kill()
            child.wait(timeout=REAP_SECONDS)
            child.stdout.close()
            with self.lock:
                if self.child is child:
                    self.child = None


_budget = None


def git(root, *args, limit=MAX_METADATA_BYTES):
    return _budget.git(root, args, limit)


def blob(root, oid, limit):
    size = int(git(root, "cat-file", "-s", oid, limit=32))
    if size < 0 or size > limit:
        raise ValueError("committed blob ceiling")
    data = git(root, "cat-file", "blob", oid, limit=limit)
    if len(data) != size:
        raise ValueError("committed size mismatch")
    return data


def bounded_file(path):
    _budget.check()
    if path.stat().st_size > MAX_SOURCE_BYTES:
        raise ValueError("source byte ceiling")
    with path.open("rb") as stream:
        if os.fstat(stream.fileno()).st_size > MAX_SOURCE_BYTES:
            raise ValueError("opened source byte ceiling")
        data = stream.read(MAX_SOURCE_BYTES + 1)
    _budget.check()
    if len(data) > MAX_SOURCE_BYTES:
        raise ValueError("source grew past ceiling")
    return data


def entry(root, tree, path):
    args = ("ls-tree", "-z", tree, "--", path) if tree else (
        "ls-files", "--stage", "-z", "--", path)
    rows = git(root, *args).split(b"\0")
    if len(rows) != 2 or rows[-1]:
        raise ValueError("not exactly one tracked entry")
    fields, name = rows[0].split(b"\t", 1)
    mode, middle, last = fields.split()
    if name.decode("utf-8") != path:
        raise ValueError("path mismatch")
    if not tree and last != b"0":
        raise ValueError("unmerged entry")
    return mode, last if tree else middle


def reparse(path):
    info = path.lstat()
    return stat.S_ISLNK(info.st_mode) or bool(
        getattr(info, "st_file_attributes", 0) & 0x400)


def plain_chain(root, path):
    relative = path.relative_to(root)
    current = root
    for component in relative.parts:
        current /= component
        if reparse(current):
            raise ValueError("nested reparse mapping")


def identity(path):
    info = path.lstat()
    return (info.st_dev, info.st_ino, info.st_mode, info.st_size,
            info.st_mtime_ns, info.st_ctime_ns)


def unchanged(root, logical):
    root = root.resolve(strict=True)
    parts = PurePosixPath(logical).parts
    if (not parts or PurePosixPath(logical).is_absolute()
            or any(p in (".", "..") for p in logical.split("/"))
            or "\\" in logical or ":" in logical
            or any(ord(c) < 32 for c in logical)):
        return False
    head = git(root, "rev-parse", "HEAD").strip().decode("ascii")
    # Only an existing HEAD directory alias can establish authority.
    for end in range(1, len(parts)):
        alias_name = "/".join(parts[:end])
        try:
            declared = entry(root, head, alias_name)
        except ValueError:
            continue
        if declared[0] != b"120000":
            continue
        if entry(root, None, alias_name) != declared:
            return False
        target_text = blob(root, declared[1].decode(), MAX_ALIAS_BYTES).decode("utf-8")
        if (not target_text or os.path.isabs(target_text) or ":" in target_text
                or "\\" in target_text or any(ord(c) < 32 for c in target_text)):
            return False
        alias = root / alias_name
        plain_chain(root, alias.parent)
        if not reparse(alias) or not alias.is_dir():
            return False
        alias_before = identity(alias)
        # Symlink text itself must be unchanged; junctions encode an absolute
        # target, so their resolved target must equal the Git declaration.
        if alias.is_symlink() and os.readlink(alias) != target_text:
            return False
        target = Path(os.path.abspath(alias.parent / target_text))
        target.relative_to(root)  # rejects escape before following anything
        plain_chain(root, target)
        if alias.resolve(strict=True) != target:
            return False
        canonical = target.joinpath(*parts[end:])
        plain_chain(root, canonical)
        canonical_name = canonical.relative_to(root).as_posix()
        if canonical_name.startswith(("src/app/", "src/lib/gc_async_mut/")):
            return False  # never exempt the canonical audited scope
        tracked = entry(root, head, canonical_name)
        if tracked[0] not in (b"100644", b"100755"):
            return False
        if entry(root, None, canonical_name) != tracked:
            return False
        attrs = git(root, "check-attr", "-z", "filter", "working-tree-encoding",
                    "--", canonical_name).split(b"\0")
        if any(attrs[i] not in (b"unspecified", b"unset")
               for i in range(2, len(attrs) - 1, 3)):
            return False
        actual = root / logical
        before = identity(canonical)
        if before[3] > MAX_SOURCE_BYTES or actual.stat().st_size > MAX_SOURCE_BYTES:
            return False
        committed = blob(root, tracked[1].decode(), MAX_SOURCE_BYTES)
        if (not os.path.samefile(actual, canonical)
                or bounded_file(canonical) != committed
                or bounded_file(actual) != committed):
            return False
        # Do not authorize a skip if declarations or objects moved while read.
        return (before == identity(canonical)
                and alias_before == identity(alias)
                and alias.resolve(strict=True) == target
                and os.path.samefile(actual, canonical)
                and git(root, "rev-parse", "HEAD").strip().decode() == head
                and entry(root, None, alias_name) == declared
                and entry(root, None, canonical_name) == tracked)
    return False


def classify(logical):
    global _budget
    _budget = Budget()
    result = [False]

    def work():
        try:
            result[0] = unchanged(Path.cwd(), logical)
        except (OSError, ValueError, UnicodeError, subprocess.SubprocessError):
            result[0] = False

    # A stuck bounded local read cannot hold the controller past its deadline.
    # The worker is read-only and cannot launch Git after cancellation.
    worker = threading.Thread(target=work, daemon=True)
    worker.start()
    worker.join(max(0, _budget.deadline - time.monotonic()))
    expired = worker.is_alive() or time.monotonic() >= _budget.deadline
    _budget.cancel()  # kills and reaps any Git child before returning
    return result[0] and not expired


if __name__ == "__main__":
    accepted = len(sys.argv) == 2 and classify(sys.argv[1])
    # Do not wait for a daemon stuck in filesystem I/O during interpreter exit.
    os._exit(0 if accepted else 1)
