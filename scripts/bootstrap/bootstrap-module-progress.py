#!/usr/bin/env python3
"""Sealed diagnostic progress, not compiler or release admission authority."""
import hashlib
import json
import os
from pathlib import Path
import sys

SCHEMA = "bootstrap-module-progress-v1"

def digest(path):
    path = Path(path)
    if path.is_symlink() or not path.is_file():
        raise ValueError("missing or symlinked evidence: " + str(path))
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def atomic(path, value):
    path = Path(path)
    tmp = path.with_name(path.name + ".tmp." + str(os.getpid()))
    with tmp.open("x", encoding="utf-8") as stream:
        stream.write(value)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(tmp, path)
    fd = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)

def machine(path, target):
    with Path(path).open("rb") as stream:
        header = stream.read(20)
    expected = {"aarch64": 183, "riscv64": 243, "riscv32": 243,
                "x86_64": 62, "i686": 3}.get(target.split("-", 1)[0])
    if expected is None or len(header) != 20 or header[:4] != b"\x7fELF":
        raise ValueError("unsupported or non-ELF diagnostic target")
    expected_class = 1 if target.startswith(("riscv32-", "i686-")) else 2
    if header[4] != expected_class or header[5] != 1:
        raise ValueError("diagnostic object ELF class/endianness mismatch")
    order = {1: "little", 2: "big"}.get(header[5])
    if order is None or int.from_bytes(header[16:18], order) != 1 or int.from_bytes(header[18:20], order) != expected:
        raise ValueError("diagnostic object target/kind mismatch")
    return expected

def row_fields(path):
    line = Path(path).read_text().strip()
    if "\n" in line:
        raise ValueError("multiline row")
    pairs = [item.split("=", 1) for item in line.split("|")]
    if any(len(pair) != 2 for pair in pairs) or len({pair[0] for pair in pairs}) != len(pairs):
        raise ValueError("malformed or duplicate row")
    return dict(pairs)

def seal_path(state, entry):
    return Path(state) / (hashlib.sha256(entry.encode()).hexdigest() + ".json")

def load_seal(path, context, entry, target):
    digest(path)
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate seal field")
            result[key] = value
        return result
    if Path(path).stat().st_size > 65536:
        raise ValueError("oversized seal")
    seal = json.loads(Path(path).read_text(), object_pairs_hook=unique)
    if set(seal) != {"schema", "context", "entry", "row", "row_sha256", "log", "log_sha256", "result", "object", "object_sha256", "machine"}:
        raise ValueError("seal shape mismatch")
    if seal["schema"] != SCHEMA or seal["context"] != context or seal["entry"] != entry:
        raise ValueError("seal binding mismatch")
    if digest(seal["row"]) != seal["row_sha256"] or digest(seal["log"]) != seal["log_sha256"]:
        raise ValueError("seal evidence changed")
    row = row_fields(seal["row"])
    if row.get("entry") != entry or row.get("result") != seal["result"] or row.get("log") != seal["log"]:
        raise ValueError("seal row mismatch")
    if seal["result"] == "PASS":
        if row.get("status") != "0" or row.get("artifact") != seal["object"] or digest(seal["object"]) != seal["object_sha256"] or machine(seal["object"], target) != seal["machine"]:
            raise ValueError("seal object mismatch")
    elif seal["result"] != "FAIL" or row.get("status") == "0" or seal["object"] is not None or seal["object_sha256"] is not None or seal["machine"] is not None:
        raise ValueError("unqualified terminal failure")
    return seal

def select(full, selected, state, context, target, limit, summary):
    if len(context) != 64 or any(ch not in "0123456789abcdef" for ch in context) or Path(state).is_symlink() or not Path(state).is_dir():
        raise ValueError("invalid progress context/state")
    entries = Path(full).read_text().splitlines()
    if not entries or len(set(entries)) != len(entries) or any(not entry or "|" in entry for entry in entries):
        raise ValueError("invalid inventory")
    pending = []
    failures = 0
    for entry in entries:
        path = seal_path(state, entry)
        if path.exists() or path.is_symlink():
            seal = load_seal(path, context, entry, target)
            failures += seal["result"] == "FAIL"
        else:
            pending.append(entry)
    chosen = pending[:limit] if limit else pending
    atomic(selected, "".join(entry + "\n" for entry in chosen))
    atomic(selected + ".unexecuted", "".join(entry + "\n" for entry in pending[len(chosen):]))
    with Path(summary).open("a") as stream:
        stream.write(f"module_compile_inventory_count={len(entries)}\nmodule_compile_selected_count={len(chosen)}\nmodule_compile_sealed_count={len(entries)-len(pending)}\nmodule_compile_retained_failed_count={failures}\nmodule_compile_unexecuted_count={len(pending)-len(chosen)}\n")
        if pending:
            stream.write(f"task=module_compile_progress|result=INCOMPLETE|status=unfinished-inventory|count={len(pending)}|log={selected}\n")
        if failures:
            stream.write(f"task=module_compile_retained_failures|result=FAIL|status=sealed-failures|count={failures}|log={state}\n")
    return bool(failures)

def publish(state, context, target, paths):
    for row_path in paths:
        row = row_fields(row_path)
        if row.get("result") not in ("PASS", "FAIL"):
            continue
        # The scheduler calls only after wait/reap and full authority validation.
        entry = row["entry"]
        path = seal_path(state, entry)
        obj = row.get("artifact") if row["result"] == "PASS" else None
        seal = dict(schema=SCHEMA, context=context, entry=entry,
                    row=str(Path(row_path).resolve()), row_sha256=digest(row_path),
                    log=row["log"], log_sha256=digest(row["log"]), result=row["result"],
                    object=obj, object_sha256=digest(obj) if obj else None,
                    machine=machine(obj, target) if obj else None)
        if path.exists() or path.is_symlink():
            load_seal(path, context, entry, target)
            raise ValueError("refusing to overwrite sealed terminal proof")
        atomic(path, json.dumps(seal, sort_keys=True) + "\n")
        load_seal(path, context, entry, target)

if __name__ == "__main__":
    try:
        cmd, *args = sys.argv[1:]
        if cmd == "lock":
            import fcntl  # POSIX only; unsupported hosts refuse explicitly.
            fcntl.flock(int(args[0]), fcntl.LOCK_EX | fcntl.LOCK_NB)
        elif cmd == "select":
            failed = select(*args[:5], int(args[5]), args[6])
            sys.exit(3 if failed else 0)
        elif cmd == "publish":
            publish(*args[:3], args[3:])
        elif cmd == "object":
            machine(*args)
        else:
            raise ValueError("unknown progress operation")
    except (ValueError, OSError, KeyError, TypeError, ImportError, RecursionError) as error:
        print("module progress refused: " + str(error), file=sys.stderr)
        sys.exit(2)
