#!/usr/bin/env python3
"""Prospective Hello gate receipt; never converts historical logs into PASS."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import struct
import sys
import tempfile


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def load(path):
    with open(path, "rb") as stream:
        data = stream.read(65537)
    require(len(data) <= 65536, "oversize JSON")
    value = json.loads(data, object_pairs_hook=pairs)
    require(type(value) is dict, "JSON must be an object")
    return value


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(65536), b""):
            h.update(block)
    return h.hexdigest()


def native_digest(path, target):
    require(target == "x86_64-unknown-linux-gnu", "unsupported receipt executable target")
    with open(path, "rb") as stream:
        header = stream.read(64)
    require(len(header) == 64 and header[:7] == b"\x7fELF\x02\x01\x01"
            and header[7] in (0, 3), "entry is not a Linux ELF64 executable")
    kind, machine, version = struct.unpack_from("<HHI", header, 16)
    require(kind in (2, 3) and machine == 62 and version == 1,
            "entry ELF executable architecture mismatch")
    return digest(path)


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args],
                                   stderr=subprocess.PIPE, timeout=30).decode().strip()


def capture(candidate, identity_path, source, runtime, backend, target, fixture, output, gate):
    identity = load(identity_path)
    required = {"schema", "compiler_sha256", "source_commit", "source_tree_oid",
                "runtime_archive_sha256", "backend", "target"}
    require(required <= identity.keys() <= required | {"producer_backend"}, "identity fields mismatch")
    require(identity["schema"] == "item5-phase2-producer-identity-v1", "identity schema mismatch")
    for key in ("compiler_sha256", "runtime_archive_sha256"):
        require(type(identity[key]) is str and re.fullmatch(r"[0-9a-f]{64}", identity[key]), "invalid hash")
    for key in ("source_commit", "source_tree_oid"):
        require(type(identity[key]) is str and re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", identity[key]), "invalid source oid")
    require(backend in ("llvm", "cranelift") and identity["backend"] == backend, "backend mismatch")
    require(re.fullmatch(r"[A-Za-z0-9_]+(?:-[A-Za-z0-9_]+){2,}", target)
            and identity["target"] == target, "target mismatch")
    require(target == "x86_64-unknown-linux-gnu", "unsupported receipt executable target")
    if "producer_backend" in identity:
        require(identity["producer_backend"] in ("llvm", "cranelift"), "invalid producer backend")
    candidate, source, runtime, fixture = map(lambda p: Path(p).resolve(strict=True),
                                            (candidate, source, runtime, fixture))
    require(candidate.is_file() and os.access(candidate, os.X_OK), "candidate not executable")
    require(runtime.is_file() and fixture.is_file(), "runtime/fixture missing")
    require(runtime.name in ("libsimple_native_all.a", "simple_native_all.lib"),
            "runtime authority must use its canonical native-all archive name")
    require(not git(source, "status", "--porcelain", "--untracked-files=normal"), "producer source is dirty")
    require(git(source, "rev-parse", "HEAD") == identity["source_commit"], "source commit mismatch")
    require(git(source, "rev-parse", "HEAD^{tree}") == identity["source_tree_oid"], "source tree mismatch")
    require(digest(candidate) == identity["compiler_sha256"], "candidate hash mismatch")
    require(digest(runtime) == identity["runtime_archive_sha256"], "runtime hash mismatch")
    output = Path(output)
    require(output.is_absolute() and output.parent.is_dir(), "receipt requires existing absolute parent")
    require(not os.path.lexists(output), "receipt already exists")
    return {"identity": identity, "identity_sha256": digest(identity_path),
            "candidate": str(candidate), "source": str(source), "runtime": str(runtime),
            "runtime_directory": str(runtime.parent),
            "fixture": str(fixture), "fixture_sha256": digest(fixture), "output": str(output),
            "gate_sha256": digest(gate), "bridge_sha256": digest(__file__)}


def status(work, name):
    raw = (work / name).read_bytes()
    require(re.fullmatch(rb"(?:0|[1-9][0-9]{0,2})\n", raw), "invalid/missing command status")
    value = int(raw)
    require(value <= 255, "status out of range")
    return value


def finish(work, snapshot):
    require(load(work / "receipt-inputs.json") == snapshot, "gate inputs changed during execution")
    require(status(work, "build-entry.status") == 0, "entry build failed")
    require(status(work, "run-entry.status") == 0, "entry execution failed")
    positional = status(work, "build-positional.status")
    require(positional < 128 and positional != 124, "positional crash/timeout")
    binary = work / "out-entry.bin"
    require(binary.is_file() and os.access(binary, os.X_OK), "entry output missing")
    before = (work / "entry-before.sha256").read_text().strip()
    require(re.fullmatch(r"[0-9a-f]{64}", before) and digest(binary) == before,
            "entry binary changed across execution")
    native_digest(binary, snapshot["identity"]["target"])
    require((work / "run-entry.stdout").stat().st_size <= 64, "entry stdout oversize")
    stdout = (work / "run-entry.stdout").read_bytes()
    require(stdout in (b"hello", b"hello\n"), "entry stdout mismatch")
    identity = snapshot["identity"]
    receipt = dict(identity)
    receipt.update(schema="item5-phase2-hello-v1", status="pass", gate_exit_status=0,
                   identity_sha256=snapshot["identity_sha256"],
                   fixture_sha256=snapshot["fixture_sha256"],
                   gate_sha256=snapshot["gate_sha256"], bridge_sha256=snapshot["bridge_sha256"],
                   artifact_directory=str(work.resolve()),
                   runtime_directory=snapshot["runtime_directory"],
                   entry={"build_exit_status": 0, "run_exit_status": 0,
                          "binary_sha256": digest(binary), "stdout_sha256": digest(work / "run-entry.stdout"),
                          "stderr_sha256": digest(work / "run-entry.stderr"),
                          "command_sha256": digest(work / "command-entry.argv"),
                          "build_log_sha256": digest(work / "build-entry.log")},
                   positional={"contract": "no-crash-no-timeout; execution not required",
                               "build_exit_status": positional,
                               "command_sha256": digest(work / "command-positional.argv"),
                               "build_log_sha256": digest(work / "build-positional.log")})
    output = Path(snapshot["output"])
    fd, temporary = tempfile.mkstemp(prefix=".hello-receipt-", dir=output.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(receipt, stream, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        # Atomic publication without replacing a stale or concurrently created receipt.
        os.link(temporary, output)
    finally:
        os.unlink(temporary)


def main():
    if len(sys.argv) == 4 and sys.argv[1] == "native-hash":
        print(native_digest(sys.argv[2], sys.argv[3]))
        return
    mode, work, *args = sys.argv[1:]
    require(mode in ("begin", "finish") and len(args) == 9, "invalid bridge invocation")
    work = Path(work)
    snapshot = capture(*args)
    if mode == "begin":
        with open(work / "receipt-inputs.json", "x", encoding="utf-8") as stream:
            json.dump(snapshot, stream, sort_keys=True)
            stream.write("\n")
    else:
        finish(work, snapshot)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print("Hello receipt rejected: " + str(error), file=sys.stderr)
        sys.exit(1)
