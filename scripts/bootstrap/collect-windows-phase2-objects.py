#!/usr/bin/env python3
"""Freeze and compile the complete Phase2 source-root object inventory.

This is a bounded diagnostic collector. A valid COFF object says only that the
requested entry produced a structurally valid AMD64 object; it is not compiler
qualification or bootstrap admission evidence.

Creating STOP_REQUEST in the work root stops new row dispatch after active rows
finish; the marker is retained and undispatched inventory rows remain PENDING.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
import uuid

TARGET = "x86_64-pc-windows-msvc"
BACKEND = "llvm"
PINNED_P2_SHA256 = "1ad6ea53c67f3e01efc5c1b0ac8aa4dcef184a0987b4d3c806c59e14e96be584"
PINNED_BOUNDED_HELPER_SHA256 = "17f0935e23cc3cf017ecde0d9769d7c4a5582be01d7ffecaa6fb8c441eac7305"
ROOTS = (
    "src/compositions/kernel_llvm_cranelift",
    "src/compiler",
    "src/app",
    "src/lib",
)
EXTERNAL_PROOF_RESERVED = {
    "src/app/bootstrap_builder/compiler_admission_diagnostic.spl",
    "src/app/doc_coverage/types/mod.spl",
}
TOOLING_PRIORITY_ROOT_COUNTS = (
    ("src/app/mcp/", 56),
    ("src/app/simple_lsp_mcp/", 12),
    ("src/app/t32_cli/", 15),
    ("src/app/mcp_t32/", 22),
    ("src/app/cmm_lsp/", 56),
    ("src/app/md_lsp/", 4),
)
STOP_REQUEST_NAME = "STOP_REQUEST"
WATCHDOG_SETUP_FAILURE_REASON = "watchdog-session-identity-install-refused"
LOG_LIMIT = 20 * 1024 * 1024
ALLOWED_STATUS = {"PENDING", "RUNNING", "PASS", "FAILED", "TIMEOUT", "UNSUPPORTED", "BLOCKED"}
OBJECT_EXT = ".obj"


class Refusal(Exception):
    pass


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def hash_file(path: Path) -> str:
    if path.is_symlink() or not path.is_file():
        raise Refusal(f"missing, non-regular, or symlinked file: {path}")
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def msys_path(path: Path) -> str:
    """Convert a resolved Windows drive path to Git/MSYS POSIX form for sh."""
    value = path.resolve(strict=True).as_posix()
    if len(value) >= 3 and value[1:3] == ":/":
        return "/" + value[0].lower() + value[2:]
    return value


def tree_identity(path: Path) -> str:
    """Hash every regular file and symlink spelling under an immutable input."""
    if not path.is_dir() or path.is_symlink():
        raise Refusal(f"input directory is unavailable or symlinked: {path}")
    rows: list[tuple[str, str, int]] = []
    for base, dirs, files in os.walk(path, followlinks=False):
        dirs.sort()
        files.sort()
        base_path = Path(base)
        for name in list(dirs):
            item = base_path / name
            if item.is_symlink():
                dirs.remove(name)
                rows.append((item.relative_to(path).as_posix(), "link:" + os.readlink(item), 0))
        for name in files:
            item = base_path / name
            rel = item.relative_to(path).as_posix()
            if item.is_symlink():
                rows.append((rel, "link:" + os.readlink(item), 0))
            elif item.is_file():
                rows.append((rel, hash_file(item), item.stat().st_size))
            else:
                raise Refusal(f"unexpected runtime/tool input type: {item}")
    digest = hashlib.sha256()
    for rel, content_sha, size in sorted(rows):
        digest.update(rel.encode("utf-8", "surrogateescape"))
        digest.update(b"\0" + content_sha.encode("utf-8", "surrogateescape"))
        digest.update(b"\0" + str(size).encode() + b"\n")
    return digest.hexdigest()


def q(value: object) -> str:
    """Quote a scalar as the JSON-compatible string subset of SDN."""
    return json.dumps(value, ensure_ascii=True, separators=(",", ":"))


def write_atomic(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + f".tmp.{os.getpid()}.{uuid.uuid4().hex}")
    with tmp.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(content)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(tmp, path)


def append_fsynced(path: Path, content: str, lock: threading.Lock) -> None:
    with lock:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8", newline="\n") as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())


def read_scalar_file(path: Path) -> dict[str, str]:
    fields: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#") or line == "records_begin" or line == "records_end":
            continue
        if "=" not in line or "|" in line:
            continue
        key, value = line.split("=", 1)
        if key in fields:
            raise Refusal(f"duplicate scalar field in receipt: {key}")
        fields[key] = value
    return fields


def decode_hex_field(record: str, name: str) -> str | None:
    match = re.search(rf"(?:^|\|){re.escape(name)}=([0-9a-f]*)\|", record)
    if not match or match.group(1) == "-":
        return None
    try:
        return bytes.fromhex(match.group(1)).decode("utf-8")
    except (ValueError, UnicodeDecodeError):
        raise Refusal(f"malformed materialization receipt field {name}")


def parse_materialization(path: Path, root: Path, revision: str) -> tuple[str, list[dict[str, str]]]:
    if path.is_symlink() or not path.is_file():
        raise Refusal("materialization receipt must be a regular file")
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    fields = read_scalar_file(path)
    expected_root = str(root.resolve()).replace("\\", "/").casefold()
    receipt_root = fields.get("root", "").replace("\\", "/").casefold()
    if receipt_root.startswith("/d/"):
        receipt_root = ("D:/" + receipt_root[3:]).casefold()
    if receipt_root != expected_root:
        raise Refusal(f"materialization receipt root mismatch: {fields.get('root', '')}")
    if fields.get("head") != revision:
        raise Refusal("materialization receipt HEAD differs from source revision")
    if fields.get("result") != "complete" or fields.get("failed") != "0":
        raise Refusal("materialization receipt is not terminal-success")
    records: list[dict[str, str]] = []
    in_records = False
    for line in text.splitlines():
        if line == "records_begin":
            in_records = True
            continue
        if line == "records_end":
            in_records = False
            continue
        if not in_records:
            continue
        item: dict[str, str] = {}
        for key in ("path", "target", "target_resolved"):
            value = decode_hex_field(line, key + "_hex")
            if value is not None:
                item[key] = value
        for key in ("target_sha256", "target_file_id", "state", "kind"):
            m = re.search(rf"(?:^|\|){key}=([^|]*)", line)
            if m:
                item[key] = m.group(1)
        if "path" in item:
            records.append(item)
    if not records and fields.get("record_count", "0") != "0":
        raise Refusal("materialization receipt records could not be parsed")
    # Any pending .spl alias inside a canonical source root makes the inventory
    # incomplete. Other pending workspace links are not source modules.
    for record in records:
        if record.get("state") != "pending_untracked":
            continue
        rel = PurePosixPath(record["path"])
        if rel.suffix == ".spl" and any(str(rel).startswith(prefix + "/") for prefix in ROOTS):
            raise Refusal(f"source alias is not materialized: {rel}")
    return sha_bytes(raw), records


def git_revision(root: Path) -> str:
    result = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, check=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    revision = result.stdout.strip()
    if not re.fullmatch(r"[0-9a-f]{40,64}", revision):
        raise Refusal("git returned an invalid source revision")
    return revision


def source_paths(root: Path) -> list[str]:
    found: list[str] = []
    for rel_root in ROOTS:
        base = root / Path(*rel_root.split("/"))
        if not base.is_dir() or base.is_symlink():
            raise Refusal(f"canonical source root missing or symlinked: {rel_root}")
        for directory, dirs, files in os.walk(base, followlinks=False):
            dirs[:] = sorted(dirs)
            for name in sorted(files):
                item = Path(directory) / name
                if item.suffix != ".spl":
                    continue
                rel = item.relative_to(root).as_posix()
                if item.is_symlink():
                    raise Refusal(f"unmaterialized source symlink: {rel}")
                if not item.is_file():
                    raise Refusal(f"source is not a regular file: {rel}")
                found.append(rel)
    found.sort()
    if not found or len(found) != len(set(found)):
        raise Refusal("source inventory is empty or contains duplicate logical paths")
    return found


def file_identity(path: Path) -> tuple[str, str]:
    resolved = path.resolve(strict=True)
    st = path.stat()
    physical = str(resolved).replace("\\", "/")
    identity = f"{st.st_dev:x}:{st.st_ino:x}"
    return physical, identity


def build_inventory(root: Path, output: Path, materialization: Path) -> Path:
    root = root.resolve(strict=True)
    output = output.resolve()
    in_build_evidence = (root / "build" / "object-campaign") == output or \
        (root / "build" / "object-campaign") in output.parents
    if (output == root or root in output.parents) and not in_build_evidence:
        raise Refusal("inventory output may be outside source root or under build/object-campaign")
    if any((root / Path(*source_root.split("/"))) == output or
           (root / Path(*source_root.split("/"))) in output.parents for source_root in ROOTS):
        raise Refusal("inventory output overlaps a canonical source root")
    revision = git_revision(root)
    materialization_sha, materialization_rows = parse_materialization(materialization, root, revision)
    paths = source_paths(root)
    rows: list[dict[str, object]] = []
    fingerprint = hashlib.sha256()
    for rel in paths:
        file_path = root / Path(*rel.split("/"))
        content_sha = hash_file(file_path)
        physical, identity = file_identity(file_path)
        row_id = sha_bytes(rel.encode("utf-8"))
        rows.append({"id": row_id, "canonical_source": rel,
                     "physical_source": physical, "source_sha256": content_sha,
                     "target": TARGET, "backend": BACKEND, "required": True,
                     "dependencies": [], "physical_file_id": identity})
        fingerprint.update(rel.encode("utf-8") + b"\0" + content_sha.encode() + b"\n")
    # Record physical aliases, while retaining every logical source row.
    id_counts: dict[str, int] = {}
    for row in rows:
        id_counts[str(row["physical_file_id"])] = id_counts.get(str(row["physical_file_id"]), 0) + 1
    aliases_by_path: dict[str, dict[str, str]] = {}
    for row in rows:
        rel = str(row["canonical_source"])
        logical_path = os.path.abspath(root / Path(*rel.split("/"))).replace("\\", "/")
        physical = str(row["physical_source"])
        if (logical_path.casefold() != physical.casefold() or
                id_counts[str(row["physical_file_id"])] > 1):
            aliases_by_path[rel] = {"logical_path": rel, "physical_source": physical,
                                    "source_sha256": str(row["source_sha256"]),
                                    "physical_file_id": str(row["physical_file_id"])}
    # Also retain logical aliases outside compilation roots from the completed
    # materializer receipt; they are metadata, never compile-row deduplication.
    for record in materialization_rows:
        rel = PurePosixPath(record["path"])
        if rel.suffix != ".spl" or not record.get("target_resolved"):
            continue
        aliases_by_path.setdefault(record["path"], {
            "logical_path": record["path"],
            "physical_source": record["target_resolved"].replace("\\", "/"),
            "source_sha256": record.get("target_sha256", ""),
            "physical_file_id": record.get("target_file_id", "")})
    aliases = sorted(aliases_by_path.values(), key=lambda row: row["logical_path"])
    alias_hash = sha_bytes("".join(
        f"{a['logical_path']}\0{a['physical_source']}\0{a['source_sha256']}\0{a['physical_file_id']}\n"
        for a in aliases).encode())
    content = [
        'schema: "objects_inventory_v1"',
        f"source_root: {q(str(root).replace(chr(92), '/'))}",
        f"source_revision: {q(revision)}",
        f"materialization_receipt: {q(str(materialization.resolve()).replace(chr(92), '/'))}",
        f"materialization_receipt_sha256: {q(materialization_sha)}",
        f"source_inventory_sha256: {q(fingerprint.hexdigest())}",
        f"alias_mapping_sha256: {q(alias_hash)}",
        f"alias_mapping_count: {len(aliases)}",
        f"target: {q(TARGET)}", f"backend: {q(BACKEND)}",
        "dependencies_complete: false",
        'excluded_roots: ["src/compiler_rust/vendor", "src/runtime/vendor", "src/runtime/miniaudio.h", "src/runtime/stb_image.h", "src/runtime/stb_truetype.h"]',
        f"row_count: {len(rows)}", "rows:",
    ]
    for row in rows:
        content.extend((f"  - id: {q(row['id'])}",
                        f"    canonical_source: {q(row['canonical_source'])}",
                        f"    physical_source: {q(row['physical_source'])}",
                        f"    physical_file_id: {q(row['physical_file_id'])}",
                        f"    source_sha256: {q(row['source_sha256'])}",
                        f"    target: {q(TARGET)}", f"    backend: {q(BACKEND)}",
                        "    required: true", "    dependencies: []"))
    content.append("aliases:")
    for alias in aliases:
        content.extend((f"  - logical_path: {q(alias['logical_path'])}",
                        f"    physical_source: {q(alias['physical_source'])}",
                        f"    physical_file_id: {q(alias['physical_file_id'])}",
                        f"    source_sha256: {q(alias['source_sha256'])}"))
    path = output / "objects_inventory_v1.sdn"
    rendered = "\n".join(content) + "\n"
    if path.exists() or path.is_symlink():
        if path.is_symlink():
            raise Refusal("refusing to replace a different frozen inventory")
        if path.read_text(encoding="utf-8") == rendered:
            return path
        if (output / "object_attempt_v1.sdn").exists():
            raise Refusal("refusing to replace inventory after attempts exist")
    write_atomic(path, rendered)
    return path


def parse_sdn(path: Path) -> tuple[dict[str, str], dict[str, list[dict[str, str]]]]:
    header: dict[str, str] = {}
    collections: dict[str, list[dict[str, str]]] = {}
    section: str | None = None
    current: dict[str, str] | None = None
    for line in path.read_text(encoding="utf-8").splitlines():
        top = re.fullmatch(r"([a-z][a-z0-9_]*):(?: (.*))?", line)
        if top:
            key, value = top.groups()
            if value is None:
                section = key
                collections.setdefault(section, [])
                current = None
            else:
                if key in header:
                    raise Refusal("duplicate SDN header field: " + key)
                header[key] = value
                section = None
                current = None
            continue
        if section and line.startswith("  - "):
            current = {}
            collections[section].append(current)
            first = re.fullmatch(r"  - ([a-z0-9_]+): (.*)", line)
            if not first:
                raise Refusal("malformed SDN list record")
            current[first.group(1)] = first.group(2)
            continue
        match = re.match(r"^    ([a-z0-9_]+): (.*)$", line)
        if section and match and current is not None:
            key, value = match.groups()
            if key in current:
                raise Refusal("duplicate field in SDN record: " + key)
            current[key] = value
            continue
        if line.strip():
            raise Refusal("unrecognized SDN structure")
    return header, collections


def unq(value: str) -> object:
    if value == "true":
        return True
    if value == "false":
        return False
    if value == "null":
        return None
    try:
        return json.loads(value)
    except json.JSONDecodeError:
        raise Refusal("malformed SDN scalar")


def load_inventory(path: Path) -> tuple[dict[str, str], list[dict[str, object]]]:
    header, collections = parse_sdn(path)
    blocks = collections.get("rows", [])
    if unq(header.get("schema", "null")) != "objects_inventory_v1":
        raise Refusal("unsupported object inventory schema")
    count = unq(header.get("row_count", "null"))
    rows: list[dict[str, object]] = []
    for block in blocks:
        row = {key: unq(value) for key, value in block.items()}
        required = {"id", "canonical_source", "physical_source", "physical_file_id",
                    "source_sha256", "target", "backend", "required", "dependencies"}
        if set(row) != required or row["target"] != TARGET or row["backend"] != BACKEND:
            raise Refusal("malformed or incompatible inventory row")
        if not isinstance(row["canonical_source"], str) or not row["canonical_source"].startswith(tuple(r + "/" for r in ROOTS)):
            raise Refusal("inventory row outside canonical source roots")
        rel = PurePosixPath(str(row["canonical_source"]))
        if ".." in rel.parts or rel.is_absolute() or row["id"] != sha_bytes(str(rel).encode("utf-8")):
            raise Refusal("inventory row ID/path binding is invalid")
        rows.append(row)
    if (not rows or count != len(rows) or
            len({row["canonical_source"] for row in rows}) != len(rows) or
            len({row["id"] for row in rows}) != len(rows)):
        raise Refusal("inventory row count/uniqueness mismatch")
    aliases = [{key: unq(value) for key, value in block.items()}
               for block in collections.get("aliases", [])]
    alias_fields = {"logical_path", "physical_source", "physical_file_id", "source_sha256"}
    if any(set(alias) != alias_fields for alias in aliases):
        raise Refusal("malformed physical alias record")
    aliases.sort(key=lambda row: str(row["logical_path"]))
    alias_text = "".join(f"{alias['logical_path']}\0{alias['physical_source']}\0{alias['source_sha256']}\0{alias['physical_file_id']}\n" for alias in aliases)
    if (unq(header.get("alias_mapping_count", "null")) != len(aliases) or
            unq(header.get("alias_mapping_sha256", "null")) != sha_bytes(alias_text.encode())):
        raise Refusal("physical alias mapping count/digest mismatch")
    rows.sort(key=lambda row: str(row["canonical_source"]))
    return header, rows


def validate_coff_section_raw_bounds(path: Path, table_offset: int,
                                    section_count: int, object_size: int) -> None:
    """Reject section raw ranges outside the object while allowing .bss."""
    with path.open("rb") as stream:
        for index in range(section_count):
            stream.seek(table_offset + index * 40)
            header = stream.read(40)
            if len(header) != 40:
                raise Refusal("truncated COFF section header")
            raw_size = int.from_bytes(header[16:20], "little")
            raw_pointer = int.from_bytes(header[20:24], "little")
            characteristics = int.from_bytes(header[36:40], "little")
            if raw_size == 0:
                continue
            if raw_pointer == 0 and characteristics & 0x00000080:
                continue
            if raw_pointer == 0 or raw_pointer > object_size or raw_size > object_size - raw_pointer:
                raise Refusal(f"COFF section {index} raw data extends beyond object bounds")


def validate_amd64_coff(path: Path) -> tuple[int, str]:
    """Validate standard AMD64 COFF or Microsoft BigObj, never PE/MZ."""
    if path.is_symlink() or not path.is_file():
        raise Refusal("object is missing, non-regular, or symlinked")
    size = path.stat().st_size
    if size < 20:
        raise Refusal("object is empty or truncated")
    with path.open("rb") as stream:
        head = stream.read(min(size, 56))
    if head[:2] == b"MZ":
        raise Refusal("PE/MZ image is not a relocatable COFF object")
    if head[:4] == b"\x00\x00\xff\xff":
        bigobj_guid = bytes.fromhex("c7a1bad1eeba a94baf20faf66aa4dcb8".replace(" ", ""))
        if len(head) < 56 or int.from_bytes(head[4:6], "little") < 2:
            raise Refusal("truncated or unsupported COFF BigObj header")
        if head[12:28] != bigobj_guid or int.from_bytes(head[6:8], "little") != 0x8664:
            raise Refusal("COFF BigObj class or machine differs from AMD64")
        section_count = int.from_bytes(head[44:48], "little")
        if section_count <= 0 or 56 + section_count * 40 > size:
            raise Refusal("COFF BigObj section table is empty or truncated")
        validate_coff_section_raw_bounds(path, 56, section_count, size)
        return size, "COFF_BIGOBJ_AMD64"
    machine = int.from_bytes(head[0:2], "little")
    sections = int.from_bytes(head[2:4], "little")
    optional_size = int.from_bytes(head[16:18], "little")
    if machine != 0x8664 or sections <= 0 or optional_size != 0 or 20 + sections * 40 > size:
        raise Refusal("standard COFF header/table is not AMD64 relocatable object")
    validate_coff_section_raw_bounds(path, 20, sections, size)
    return size, "COFF_AMD64"


def documentation_only(path: Path) -> bool:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (UnicodeError, OSError):
        return False
    return all(not line.strip() or line.lstrip().startswith("#") for line in lines)


def load_attempt_events(path: Path) -> list[dict[str, object]]:
    if not path.exists():
        return []
    header, collections = parse_sdn(path)
    if unq(header.get("schema", "null")) != "object_attempt_v1":
        raise Refusal("unsupported attempt journal schema")
    blocks = collections.get("events", [])
    events: list[dict[str, object]] = []
    for block in blocks:
        events.append({key: unq(value) for key, value in block.items()})
    return events


def index_attempt_events(events: list[dict[str, object]]) -> tuple[
        dict[str, dict[str, object]], dict[str, int]]:
    """Return the latest event and terminal-attempt count for each inventory row."""
    latest: dict[str, dict[str, object]] = {}
    counts: dict[str, int] = {}
    terminal_statuses = {"PASS", "FAILED", "TIMEOUT", "UNSUPPORTED", "BLOCKED"}
    for event in events:
        row_id = event.get("row_id")
        if not isinstance(row_id, str):
            continue
        latest[row_id] = event
        if event.get("status") in terminal_statuses:
            counts[row_id] = counts.get(row_id, 0) + 1
    return latest, counts


def pending_state_rows(rows: list[dict[str, object]],
                       terminal: dict[str, str]) -> list[dict[str, object]]:
    """Select only rows that need an explicit PENDING pre-dispatch receipt."""
    return [row for row in rows if terminal.get(str(row["id"]), "PENDING") == "PENDING"]


def render_record(values: dict[str, object]) -> str:
    fields = []
    for key, value in values.items():
        if isinstance(value, list):
            encoded = "[" + ", ".join(q(item) for item in value) + "]"
        elif value is None:
            encoded = "null"
        elif isinstance(value, bool):
            encoded = "true" if value else "false"
        elif isinstance(value, int):
            encoded = str(value)
        else:
            encoded = q(str(value))
        fields.append(f"    {key}: {encoded}")
    if not fields:
        raise Refusal("empty SDN record")
    fields[0] = "  - " + fields[0].strip()
    return "\n".join(fields) + "\n"


def env_identity(env: dict[str, str], compiler: Path,
                 runtime: Path, tools: Path) -> tuple[str, str, str, str, str]:
    producer_sha = hash_file(compiler)
    runtime_id = tree_identity(runtime)
    tools_id = tree_identity(tools)
    relevant = {key: value for key, value in env.items()
                if key.upper() in {"PATH", "INCLUDE", "LIB", "LIBPATH", "SYSTEMROOT",
                                   "CC", "CXX", "CL", "LINK", "VSLANG", "LLVM_HOME",
                                   "VSINSTALLDIR", "VCINSTALLDIR", "VCTOOLSDIR", "VCTOOLSVERSION",
                                   "WINDOWSSDKDIR", "WINDOWSSDKVERSION", "UNIVERSALCRTSDKDIR",
                                   "UCRTVERSION",
                                   "SIMPLE_NATIVE_BUILD_EMIT_OBJECT", "SIMPLE_BOOTSTRAP_RSS_CAP_MODE",
                                   "SIMPLE_SCV_INVENTORY_COLD_INIT",
                                   "SIMPLE_CC", "SIMPLE_NM", "SIMPLE_WINDOWS_ABI",
                                   "SIMPLE_NATIVE_RUNTIME_BUNDLE", "SIMPLE_NATIVE_BUILD_THREADS",
                                   "SIMPLE_NATIVE_BUILD_TARGET", "SIMPLE_RUNTIME_PATH", "SIMPLE_BINARY",
                                   "SIMPLE_PROJECT_ROOT", "SIMPLE_LIB", "SIMPLE_ABI_POLICY",
                                   "SIMPLE_RUNTIME_RISCV64_VECTOR", "SIMPLE_BOOTSTRAP_STAGE3",
                                   "SIMPLE_BOOTSTRAP_STAGE4", "SIMPLE_NO_STUB_FALLBACK"}}
    relevant["toolchain_dir"] = str(tools.resolve())
    relevant["SIMPLE_LINK_OBJECTS"] = "__unset__"
    return producer_sha, runtime_id, tools_id, tool_id_hash(tools_id, relevant), sha_bytes(json.dumps(relevant, sort_keys=True).encode())


def safe_env_identity(env: dict[str, str], compiler: Path,
                      runtime: Path, tools: Path) -> tuple[str, str, str, str, str]:
    try:
        return env_identity(env, compiler, runtime, tools)
    except (OSError, Refusal):
        return "", "", "", "", ""


def tool_id_hash(tools_hash: str, relevant: dict[str, str]) -> str:
    return sha_bytes((tools_hash + "\n" + json.dumps(relevant, sort_keys=True)).encode())


def log_excerpt(path: Path, limit: int = 4096) -> str:
    """Return bounded head, terminal diagnostics and tail context from a log."""
    try:
        size = path.stat().st_size
        with path.open("rb") as stream:
            head = stream.read(min(512, size)).decode("utf-8", "replace")
            stream.seek(max(0, size - 64 * 1024))
            tail = stream.read(64 * 1024).decode("utf-8", "replace")
    except OSError:
        return "log-unavailable"
    diagnostics = [line for line in tail.splitlines()
                   if re.search(r"\[ERROR\]|\berror:|parse error|HIR lowering|MIR lowering|unresolved",
                                line, re.IGNORECASE)]
    body = ("HEAD:\n" + head.strip() + "\nDIAGNOSTICS:\n" +
            "\n".join(diagnostics[-8:]) + "\nTAIL:\n" + tail[-1200:].strip()).strip()
    if len(body) <= limit:
        return body
    marker = "\n... excerpt bounded ...\n"
    remaining = max(0, limit - len(marker))
    prefix_size = min(512, remaining // 4)
    return body[:prefix_size] + marker + body[-(remaining - prefix_size):]


def classify_watchdog_setup_failure_v1(exit_code: int | None, supervisor_text: str,
                                       rss_values: dict[str, str],
                                       collector_receipt_present: bool) -> bool:
    """Recognize only the evidenced pre-compiler watchdog identity refusal."""
    if exit_code != 89 or collector_receipt_present:
        return False
    supervisor = supervisor_text.lower()
    refusal = "rss-guard: session installation failed: cannot record compiler identity"
    if refusal not in supervisor:
        return False
    if (rss_values.get("status") != "session-helper-install-failed" or
            rss_values.get("exit_status") != "89" or
            rss_values.get("root_pid") != "0" or
            rss_values.get("samples") != "0"):
        return False
    return True


def take_dispatch_row(entries: list[dict[str, object]], cursor_state: list[int],
                      cursor_lock: threading.Lock, stop: threading.Event,
                      deadline: float, stop_request_path: Path,
                      now: float | None = None) -> tuple[dict[str, object] | None, bool]:
    """Atomically check stop/deadline and reserve exactly one undispatched row."""
    if len(cursor_state) != 1:
        raise Refusal("dispatch cursor state must contain exactly one position")
    with cursor_lock:
        cursor = cursor_state[0]
        if stop.is_set() or (time.monotonic() if now is None else now) >= deadline:
            return None, False
        if stop_request_path.exists():
            stop.set()
            return None, True
        if cursor >= len(entries):
            return None, False
        cursor_state[0] = cursor + 1
        return entries[cursor], False


def apply_priority_manifest(rows: list[dict[str, object]], path: Path,
                            inventory_sha256: str) -> list[dict[str, object]]:
    """Validate the reviewed 165-row cohort and order it before the full remainder."""
    if path.is_symlink() or not path.is_file():
        raise Refusal("priority manifest must be a regular non-symlink file")
    manifest_sha_before = hash_file(path)
    header, collections = parse_sdn(path)
    if unq(header.get("schema", "null")) != "tooling_priority_cohort_v1":
        raise Refusal("unsupported tooling priority cohort schema")
    if unq(header.get("inventory_sha256", "null")) != inventory_sha256:
        raise Refusal("priority cohort is bound to a different frozen inventory")
    if (unq(header.get("priority_count", "null")) != 165 or
            unq(header.get("remainder_count", "null")) != 14813 or
            unq(header.get("inventory_row_count", "null")) != 14978):
        raise Refusal("priority cohort counts do not match the complete frozen inventory")
    if (unq(header.get("priority_ids_unique", "false")) is not True or
            unq(header.get("priority_remainder_disjoint", "false")) is not True or
            unq(header.get("priority_plus_remainder_equals_inventory", "false")) is not True):
        raise Refusal("priority cohort partition assertions are absent or false")

    roots = [{key: unq(value) for key, value in block.items()}
             for block in collections.get("roots", [])]
    expected_roots = [{"path": root, "count": count}
                      for root, count in TOOLING_PRIORITY_ROOT_COUNTS]
    if roots != expected_roots:
        raise Refusal("priority cohort roots/counts differ from the reviewed tooling roots")

    blocks = collections.get("priority_rows", [])
    priority = [{key: unq(value) for key, value in block.items()} for block in blocks]
    required_fields = {"row_id", "canonical_source", "physical_source", "source_sha256"}
    if len(priority) != 165 or any(set(row) != required_fields for row in priority):
        raise Refusal("priority cohort must contain exactly 165 fully bound logical rows")
    priority_ids = [str(row["row_id"]) for row in priority]
    priority_paths = [str(row["canonical_source"]) for row in priority]
    if len(set(priority_ids)) != 165 or len(set(priority_paths)) != 165:
        raise Refusal("priority cohort contains duplicate logical IDs or paths")
    for root, expected_count in TOOLING_PRIORITY_ROOT_COUNTS:
        actual_count = sum(path.startswith(root) for path in priority_paths)
        if actual_count != expected_count:
            raise Refusal(f"priority cohort has {actual_count} rows under {root}; expected {expected_count}")
    if any(not any(path.startswith(root) for root, _ in TOOLING_PRIORITY_ROOT_COUNTS)
           for path in priority_paths):
        raise Refusal("priority cohort contains a row outside the six reviewed tooling roots")

    inventory_by_id = {str(row["id"]): row for row in rows}
    for item in priority:
        row = inventory_by_id.get(str(item["row_id"]))
        if (row is None or item["canonical_source"] != row["canonical_source"] or
                item["physical_source"] != row["physical_source"] or
                item["source_sha256"] != row["source_sha256"]):
            raise Refusal("priority row does not match the frozen inventory ID/path/source binding")
    expected_priority_ids = [str(row["id"]) for row in rows
                             if str(row["id"]) in set(priority_ids)]
    if priority_ids != expected_priority_ids:
        raise Refusal("priority rows are not in stable frozen inventory order")

    priority_set = set(priority_ids)
    remainder = [row for row in rows if str(row["id"]) not in priority_set]
    if len(rows) != 14978 or len(remainder) != 14813:
        raise Refusal("priority plus remainder does not cover all 14,978 inventory rows")
    ordered = [inventory_by_id[row_id] for row_id in priority_ids] + remainder
    if len({str(row["id"]) for row in ordered}) != len(rows):
        raise Refusal("priority scheduling order lost or duplicated inventory rows")
    if hash_file(path) != manifest_sha_before:
        raise Refusal("priority manifest changed while it was being validated")
    return ordered


def collect(args: argparse.Namespace) -> int:
    inventory_path = args.inventory.resolve(strict=True)
    work = args.work_root.resolve()
    cache_root = args.cache_root.resolve()
    producer = args.producer.resolve(strict=True)
    runtime = args.runtime_capsule.resolve(strict=True)
    tools = args.toolchain_dir.resolve(strict=True)
    if not producer.is_file() or producer.is_symlink():
        raise Refusal("pinned producer must be a regular file")
    source_arg_root = args.source_root.resolve(strict=True)
    evidence_root = source_arg_root / "build" / "object-campaign"
    if any((source_arg_root == base or source_arg_root in base.parents) and
           not (base == evidence_root or evidence_root in base.parents)
           for base in (work, cache_root)):
        raise Refusal("work/cache roots must be outside source roots or under build/object-campaign")
    header, rows = load_inventory(inventory_path)
    schedule_rows = rows
    priority_manifest_sha256: str | None = None
    if args.priority_manifest is not None:
        priority_manifest_sha256 = hash_file(args.priority_manifest)
        schedule_rows = apply_priority_manifest(rows, args.priority_manifest,
                                                hash_file(inventory_path))
    source_root = Path(str(unq(header["source_root"]))).resolve(strict=True)
    if args.source_root.resolve(strict=True) != source_root:
        raise Refusal("source root differs from inventory")
    if git_revision(source_root) != unq(header["source_revision"]):
        raise Refusal("source revision changed after inventory freeze")
    materialization = Path(str(unq(header["materialization_receipt"]))).resolve(strict=True)
    if hash_file(materialization) != unq(header["materialization_receipt_sha256"]):
        raise Refusal("materialization receipt changed after inventory freeze")
    if hash_file(producer) != PINNED_P2_SHA256:
        raise Refusal("producer is not the pinned Phase2 compiler")
    capsule_verifier = source_root / "scripts/bootstrap/phase2-runtime-capsule.shs"
    shell = shutil.which("sh")
    if not shell:
        raise Refusal("Git/MSYS sh is unavailable on PATH for canonical capsule verification")
    verify_argv = [shell, msys_path(capsule_verifier), "verify", msys_path(runtime)]
    verify = subprocess.run(verify_argv, cwd=source_root, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True)
    if verify.returncode != 0:
        diagnostic = (verify.stderr.strip() or verify.stdout.strip())[-1200:]
        raise Refusal(f"runtime capsule failed canonical Phase2 verification (exit {verify.returncode}; "
                      f"argv={verify_argv!r}): {diagnostic or 'no verifier output'}")
    capsule_fields = read_scalar_file(runtime / "phase2-runtime-capsule.env")
    if capsule_fields.get("compiler_sha256") != hash_file(producer):
        raise Refusal("runtime capsule does not bind the pinned producer")
    work.mkdir(parents=True, exist_ok=True)
    cache_root.mkdir(parents=True, exist_ok=True)
    lock_path = work / "object-campaign.lock"
    try:
        lock_file = lock_path.open("x", encoding="utf-8")
    except FileExistsError:
        raise Refusal("campaign lock exists; require owner quiescence before resume")
    with lock_file:
        lock_file.write(f"pid={os.getpid()}\nstarted_epoch={int(time.time())}\n")
        lock_file.flush()
        os.fsync(lock_file.fileno())
    attempt_path = work / "object_attempt_v1.sdn"
    cause_path = work / "cause_ledger_v1.sdn"
    if not attempt_path.exists():
        write_atomic(attempt_path, 'schema: "object_attempt_v1"\nevents:\n')
    if not cause_path.exists():
        write_atomic(cause_path, 'schema: "cause_ledger_v1"\ncauses:\n')
    old_events = load_attempt_events(attempt_path)
    latest, counts = index_attempt_events(old_events)

    env_base = os.environ.copy()
    env_base["PATH"] = str(tools) + os.pathsep + env_base.get("PATH", "")
    cc = tools / "clang-cl.exe"
    nm = tools / "llvm-nm.exe"
    if not cc.is_file() or not nm.is_file():
        raise Refusal("toolchain directory must contain clang-cl.exe and llvm-nm.exe")
    env_base.update({"SIMPLE_BOOTSTRAP_RSS_CAP_MODE": "enforce",
                     "SIMPLE_NATIVE_BUILD_EMIT_OBJECT": "1",
                     "SIMPLE_NATIVE_RUNTIME_BUNDLE": "core-c-bootstrap",
                     "SIMPLE_NATIVE_BUILD_THREADS": "1",
                     "SIMPLE_CC": str(cc), "CC": str(cc),
                     "SIMPLE_NM": str(nm), "SIMPLE_WINDOWS_ABI": "msvc",
                     "SIMPLE_SCV_INVENTORY_COLD_INIT": "1",
                     "SIMPLE_NATIVE_BUILD_TARGET": TARGET,
                     "SIMPLE_BINARY": str(producer),
                     "SIMPLE_PROJECT_ROOT": str(source_root),
                     "SIMPLE_LIB": str(source_root / "src"),
                     "SIMPLE_ABI_POLICY": "v1",
                     "SIMPLE_RUNTIME_RISCV64_VECTOR": "0",
                     "SIMPLE_BOOTSTRAP_STAGE3": "0",
                     "SIMPLE_BOOTSTRAP_STAGE4": "0",
                     "SIMPLE_NO_STUB_FALLBACK": "1"})
    for ambient in ("SIMPLE_BOOTSTRAP", "SIMPLE_NATIVE_BUILD_RUST",
                    "SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE", "SIMPLE_NATIVE_BUILD_WORKER"):
        env_base.pop(ambient, None)
    env_base.pop("SIMPLE_LINK_OBJECTS", None)
    producer_sha, runtime_id, tools_id, tool_id, env_id = env_identity(env_base, producer, runtime, tools)
    helper = source_root / "scripts/bootstrap/run-process-group-bounded-log-windows.py"
    if hash_file(helper) != PINNED_BOUNDED_HELPER_SHA256:
        raise Refusal("bounded Windows process collector differs from its reviewed hash")
    current_entries: list[dict[str, object]] = []
    terminal: dict[str, str] = {}
    for row in schedule_rows:
        rel = str(row["canonical_source"])
        source = source_root / Path(*rel.split("/"))
        current_sha = hash_file(source)
        if current_sha != row["source_sha256"]:
            raise Refusal(f"source changed since inventory freeze: {rel}")
        if rel in EXTERNAL_PROOF_RESERVED:
            terminal[str(row["id"])] = "PENDING"
            continue
        prior = latest.get(str(row["id"]))
        same_inputs = (prior is not None and prior.get("source_sha256") == row["source_sha256"] and
                       prior.get("source_snapshot_sha256") == unq(header["source_inventory_sha256"]) and
                       prior.get("alias_mapping_sha256") == unq(header["alias_mapping_sha256"]) and
                       prior.get("producer_sha256") == producer_sha and
                       prior.get("runtime_identity") == runtime_id and
                       prior.get("tool_identity") == tool_id and
                       prior.get("environment_identity") == env_id and
                       prior.get("target") == TARGET and prior.get("backend") == BACKEND)
        if same_inputs and prior and prior.get("status") == "PASS":
            obj = Path(str(prior.get("object_path", "")))
            try:
                size, kind = validate_amd64_coff(obj)
                same_object = size == prior.get("object_bytes") and hash_file(obj) == prior.get("object_sha256")
            except (OSError, Refusal):
                same_object = False
            if same_object:
                terminal[str(row["id"])] = "PASS"
                continue
        if same_inputs and prior and prior.get("status") in {"FAILED", "TIMEOUT", "UNSUPPORTED", "BLOCKED"}:
            terminal[str(row["id"])] = str(prior["status"])
            continue
        if counts.get(str(row["id"]), 0) >= 6:
            terminal[str(row["id"])] = "FAILED"
            continue
        current_entries.append(row)

    inventory_ids = {str(row["id"]) for row in rows}
    selected_ids = {str(row["id"]) for row in current_entries}
    terminal_ids = set(terminal)
    if selected_ids & terminal_ids or selected_ids | terminal_ids != inventory_ids:
        raise Refusal("row selection did not partition the complete frozen inventory")

    campaign = uuid.uuid4().hex
    start = time.monotonic()
    deadline = start + args.epoch_timeout_seconds
    stop = threading.Event()
    append_lock = threading.Lock()
    cursor_lock = threading.Lock()
    cursor_state = [0]
    stop_request_seen = False
    log_root = work / "logs" / campaign
    output_root = work / "objects" / campaign
    temp_root = work / "tmp" / campaign
    rss_root = work / "rss" / campaign
    for directory in (log_root, output_root, temp_root, rss_root):
        directory.mkdir(parents=True, exist_ok=True)
    cache_locks: list[Path] = []
    try:
        for lane in range(args.workers):
            lane_lock = cache_root / f"worker-{lane}.writer.lock"
            with lane_lock.open("x", encoding="utf-8") as stream:
                stream.write(f"campaign={campaign}\npid={os.getpid()}\n")
                stream.flush()
                os.fsync(stream.fileno())
            cache_locks.append(lane_lock)
    except FileExistsError:
        for lane_lock in cache_locks:
            lane_lock.unlink(missing_ok=True)
        raise Refusal("worker cache writer lock exists")
    wd = source_root / "scripts/resource/process-tree-rss-watchdog.pl"
    if not wd.is_file():
        raise Refusal("existing process-tree RSS watchdog is unavailable")
    perl = shutil.which("perl")
    python = sys.executable
    if not perl:
        raise Refusal("Perl required by the existing Windows process-tree watchdog is unavailable")

    stop_request_path = work / STOP_REQUEST_NAME

    def next_row() -> dict[str, object] | None:
        nonlocal stop_request_seen
        row, stop_seen = take_dispatch_row(
            current_entries, cursor_state, cursor_lock, stop, deadline, stop_request_path)
        if stop_seen:
            stop_request_seen = True
        return row

    def append_event(values: dict[str, object]) -> None:
        append_fsynced(attempt_path, render_record(values), append_lock)

    # Record only undispatched PENDING rows. Reused terminal receipts, especially
    # PASS objects, stay the latest full proof record for their inventory row.
    pending_records = []
    for row in rows:
        row_id = str(row["id"])
        terminal.setdefault(row_id, "PENDING")
    for row in pending_state_rows(rows, terminal):
        row_id = str(row["id"])
        pending_records.append(render_record({"campaign_id": campaign, "row_id": row_id,
                      "canonical_source": row["canonical_source"],
                      "source_sha256": row["source_sha256"],
                      "source_snapshot_sha256": unq(header["source_inventory_sha256"]),
                      "alias_mapping_sha256": unq(header["alias_mapping_sha256"]),
                      "producer_sha256": producer_sha, "runtime_identity": runtime_id,
                      "tool_identity": tool_id, "environment_identity": env_id,
                      "target": TARGET, "backend": BACKEND,
                      "cache_owner": "unassigned", "cache_root": str(cache_root),
                      "argv": [], "exit_code": None, "elapsed_ms": 0,
                       "peak_rss_kib": None, "stage": "UNKNOWN", "status": "PENDING",
                      "object_path": None, "object_bytes": None, "object_sha256": None,
                       "log_path": None,
                       "reason": ("external-proof-reserved" if row["canonical_source"] in EXTERNAL_PROOF_RESERVED
                                  else "campaign-row-state")}))
    append_fsynced(attempt_path, "".join(pending_records), append_lock)

    def process_lane(lane: int) -> None:
        nonlocal producer_sha, runtime_id, tool_id, env_id
        cache_owner = f"worker-{lane}"
        worker_cache = cache_root / cache_owner
        worker_cache.mkdir(parents=True, exist_ok=True)
        while True:
            row = next_row()
            if row is None:
                return
            row_id = str(row["id"])
            rel = str(row["canonical_source"])
            source = source_root / Path(*rel.split("/"))
            row_dir = output_root / row_id
            row_dir.mkdir(parents=True, exist_ok=True)
            log_path = row_dir / "compiler.log"
            object_path = row_dir / (Path(rel).stem + OBJECT_EXT)
            rss_receipt = rss_root / f"{row_id}.rss.env"
            row_start = time.monotonic()
            source_before = hash_file(source)
            if source_before != row["source_sha256"]:
                terminal[row_id] = "BLOCKED"
                append_event({"campaign_id": campaign, "row_id": row_id,
                              "canonical_source": rel, "source_sha256": row["source_sha256"],
                              "source_snapshot_sha256": unq(header["source_inventory_sha256"]),
                              "alias_mapping_sha256": unq(header["alias_mapping_sha256"]),
                              "producer_sha256": producer_sha, "runtime_identity": runtime_id,
                              "tool_identity": tool_id, "environment_identity": env_id,
                              "target": TARGET, "backend": BACKEND,
                              "bounded_helper_sha256": PINNED_BOUNDED_HELPER_SHA256,
                              "cache_owner": cache_owner, "cache_root": str(worker_cache),
                              "argv": [], "exit_code": None, "elapsed_ms": 0,
                              "peak_rss_kib": None, "stage": "UNKNOWN", "status": "BLOCKED",
                              "object_path": None, "object_bytes": None, "object_sha256": None,
                              "log_path": str(log_path), "reason": "source-changed-before-row"})
                continue
            if documentation_only(source):
                terminal[row_id] = "UNSUPPORTED"
                note = "blank-or-comment-only-source-has-no-object-output\n"
                write_atomic(log_path, note)
                append_event({"campaign_id": campaign, "row_id": row_id,
                              "canonical_source": rel, "source_sha256": source_before,
                              "source_snapshot_sha256": unq(header["source_inventory_sha256"]),
                              "alias_mapping_sha256": unq(header["alias_mapping_sha256"]),
                              "producer_sha256": producer_sha, "runtime_identity": runtime_id,
                              "tool_identity": tool_id, "environment_identity": env_id,
                              "target": TARGET, "backend": BACKEND,
                              "bounded_helper_sha256": PINNED_BOUNDED_HELPER_SHA256,
                              "cache_owner": cache_owner, "cache_root": str(worker_cache),
                              "argv": [], "exit_code": None, "elapsed_ms": 0,
                              "peak_rss_kib": None, "stage": "UNKNOWN", "status": "UNSUPPORTED",
                              "object_path": None, "object_bytes": None, "object_sha256": None,
                              "log_path": str(log_path), "reason": "documentation-only-no-code"})
                continue
            remaining = int(deadline - time.monotonic())
            if remaining <= 5:
                stop.set()
                return
            row_timeout = min(args.row_timeout_seconds, remaining - 5)
            row_tmp = temp_root / row_id
            row_tmp.mkdir(parents=True, exist_ok=True)
            env = env_base.copy()
            env["HOME"] = str(row_tmp / "home")
            env["USERPROFILE"] = str(row_tmp / "home")
            env["TMP"] = str(row_tmp)
            env["TEMP"] = str(row_tmp)
            env["TMPDIR"] = str(row_tmp)
            (row_tmp / "home").mkdir(parents=True, exist_ok=True)
            native_cache = worker_cache / "native"
            frontend_cache = worker_cache / "frontend"
            hir_cache = worker_cache / "hir"
            runtime_obj_cache = worker_cache / "runtime-objects"
            for cache in (native_cache, frontend_cache, hir_cache, runtime_obj_cache):
                cache.mkdir(parents=True, exist_ok=True)
            env.update({
                "SIMPLE_NATIVE_RUNTIME_BUNDLE": "core-c-bootstrap",
                "SIMPLE_RUNTIME_PATH": str(runtime),
                "SIMPLE_CC": str(cc), "CC": str(cc),
                "SIMPLE_NM": str(nm), "SIMPLE_WINDOWS_ABI": "msvc",
                "SIMPLE_NATIVE_BUILD_THREADS": "1",
                "SIMPLE_NATIVE_BUILD_CACHE_DIR": str(native_cache),
                "SIMPLE_FRONTEND_CACHE": "1",
                "SIMPLE_FRONTEND_CACHE_DIR": str(frontend_cache),
                "SIMPLE_HIR_CACHE": "1",
                "SIMPLE_HIR_CACHE_DIR": str(hir_cache),
                "SIMPLE_RT_OBJ_CACHE_DIR": str(runtime_obj_cache),
                "SIMPLE_NATIVE_BUILD_TARGET": TARGET,
                "SIMPLE_BINARY": str(producer),
                "SIMPLE_PROJECT_ROOT": str(source_root),
                "SIMPLE_LIB": str(source_root / "src"),
                "SIMPLE_ABI_POLICY": "v1",
                "SIMPLE_RUNTIME_RISCV64_VECTOR": "0",
                "SIMPLE_BOOTSTRAP_STAGE3": "0",
                "SIMPLE_BOOTSTRAP_STAGE4": "0",
                "SIMPLE_NO_STUB_FALLBACK": "1",
            })
            for ambient in ("SIMPLE_BOOTSTRAP", "SIMPLE_NATIVE_BUILD_RUST",
                            "SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE", "SIMPLE_NATIVE_BUILD_WORKER"):
                env.pop(ambient, None)
            command = [str(producer), "native-build", str(source), "--emit-object",
                       "--runtime-bundle", "core-c-bootstrap", "--backend", BACKEND,
                       "--target", TARGET, "--runtime-path", str(runtime),
                       "--cache-dir", str(native_cache), "--threads", "1",
                       "--go-to-end", "--output", str(object_path)]
            adapter_receipt = row_dir / "collector.sdn"
            supervisor_path = row_dir / "supervisor.log"
            adapter_command = [python, str(helper), "--output-parent", str(row_dir),
                               "--log-leaf", "compiler.log", "--receipt-leaf", "collector.sdn",
                               f"--helper-sha256={PINNED_BOUNDED_HELPER_SHA256}",
                               f"--max-bytes={LOG_LIMIT}", f"--timeout-seconds={row_timeout}",
                               "--term-grace-seconds=5", "--command-environment", "inherited",
                               "--root-exit-policy", "wait-job", "--", *command]
            watchdog_command = [perl, str(wd), f"--max-rss-kib={args.max_rss_kib}",
                                "--compiler-jobs=1", "--interval-ms=100",
                                "--rss-cap-mode=enforce", "--cap-source=explicit-env",
                                "--cap-bound=explicit", f"--timeout-seconds={row_timeout + 10}",
                                "--term-grace-seconds=5", f"--receipt={rss_receipt}",
                                "--", *adapter_command]
            attempt_base = {"campaign_id": campaign, "row_id": row_id,
                            "canonical_source": rel, "source_sha256": source_before,
                            "source_snapshot_sha256": unq(header["source_inventory_sha256"]),
                            "alias_mapping_sha256": unq(header["alias_mapping_sha256"]),
                            "producer_sha256": producer_sha, "runtime_identity": runtime_id,
                            "tool_identity": tool_id, "environment_identity": env_id,
                            "target": TARGET, "backend": BACKEND,
                            "bounded_helper_sha256": PINNED_BOUNDED_HELPER_SHA256,
                            "cache_owner": cache_owner, "cache_root": str(worker_cache),
                            "argv": watchdog_command, "exit_code": None, "elapsed_ms": 0,
                            "peak_rss_kib": None, "stage": "UNKNOWN", "status": "RUNNING",
                            "object_path": str(object_path), "object_bytes": None,
                            "object_sha256": None, "log_path": str(log_path)}
            append_event(attempt_base)
            code: int | None = None
            try:
                with supervisor_path.open("xb") as stdout:
                    process = subprocess.run(watchdog_command, cwd=source_root, env=env,
                                             stdin=subprocess.DEVNULL, stdout=stdout,
                                             stderr=subprocess.STDOUT, check=False)
                    code = process.returncode
            except (OSError, subprocess.SubprocessError) as error:
                code = 127
                with log_path.open("a", encoding="utf-8") as log:
                    log.write(f"collector launch failure: {error}\n")
            elapsed_ms = int((time.monotonic() - row_start) * 1000)
            source_after = hash_file(source)
            producer_after = hash_file(producer)
            if hash_file(helper) != PINNED_BOUNDED_HELPER_SHA256:
                raise Refusal("bounded process helper changed during row")
            # Producer/source are cheap per-row pins. Capsule/toolchain trees
            # are hashed at the campaign start and terminal boundary.
            source_stable = source_after == source_before
            authority_stable = producer_after == producer_sha
            rss_values = read_scalar_file(rss_receipt) if rss_receipt.exists() else {}
            adapter_values = read_scalar_file(adapter_receipt) if adapter_receipt.exists() else {}
            supervisor_text = (supervisor_path.read_text(encoding="utf-8", errors="replace")
                               if supervisor_path.exists() else "")
            watchdog_setup_refused = classify_watchdog_setup_failure_v1(
                code, supervisor_text, rss_values, adapter_receipt.exists())
            peak = int(rss_values["peak_rss_kib"]) if rss_values.get("peak_rss_kib", "").isdigit() else None
            size = obj_sha = object_kind = None
            if not source_stable or not authority_stable:
                status, reason = "BLOCKED", "source-or-authority-changed-during-row"
            elif watchdog_setup_refused:
                status, reason = "BLOCKED", WATCHDOG_SETUP_FAILURE_REASON
            elif code == 124 or adapter_values.get("reason") == "timeout" or rss_values.get("status") in {"timeout", "timed-out", "time-limit-exceeded"}:
                status, reason = "TIMEOUT", "row-deadline"
            elif code == 0:
                try:
                    size, object_kind = validate_amd64_coff(object_path)
                    obj_sha = hash_file(object_path)
                    stage = "OBJECT"
                    status, reason = "PASS", "validated-amd64-coff"
                except (OSError, Refusal) as error:
                    size, obj_sha, stage, object_kind = None, None, "UNKNOWN", None
                    status, reason = "FAILED", "invalid-or-missing-object: " + str(error)
            else:
                size, obj_sha, stage, object_kind = None, None, "UNKNOWN", None
                status, reason = "FAILED", f"compiler-or-watchdog-exit-{code}"
            if status != "PASS":
                size, obj_sha = None, None
                stage = "UNKNOWN"
            terminal[row_id] = status
            final = dict(attempt_base)
            final.update({"exit_code": code, "elapsed_ms": elapsed_ms,
                          "peak_rss_kib": peak, "stage": stage, "status": status,
                          "object_kind": object_kind,
                          "object_bytes": size, "object_sha256": obj_sha,
                          "reason": reason, "rss_receipt": str(rss_receipt),
                          "supervisor_log_path": str(supervisor_path),
                          "rss_status": rss_values.get("status", "unavailable"),
                          "bounded_log_receipt": str(adapter_receipt),
                          "bounded_log_status": adapter_values.get("status", "unavailable"),
                          "bounded_log_reason": adapter_values.get("reason", "unavailable")})
            append_event(final)
            if status in {"FAILED", "TIMEOUT", "BLOCKED"}:
                attempts = counts.get(row_id, 0) + 1
                cause_log_path = supervisor_path if watchdog_setup_refused else log_path
                cause = {"campaign_id": campaign, "row_id": row_id,
                         "canonical_source": rel, "original_failure": reason,
                         "bug_id": None, "attempt_count": attempts,
                         "changed_inputs": [], "cache_removal_check": "not-performed",
                         "stage": stage, "log_path": str(cause_log_path),
                         "compiler_log_path": str(log_path),
                         "log_excerpt": log_excerpt(cause_log_path), "source_sha256": source_before,
                         "producer_sha256": producer_sha, "runtime_identity": runtime_id,
                         "tool_identity": tool_id}
                append_fsynced(cause_path, render_record(cause), append_lock)
                counts[row_id] = attempts
            # Recheck campaign-level authorities at each finished row boundary.
            if git_revision(source_root) != unq(header["source_revision"]):
                stop.set()
            if int(time.monotonic() - start) >= args.epoch_timeout_seconds:
                stop.set()

    # Two long-lived lanes each own an isolated mutable compiler/runtime cache.
    lane_errors: list[str] = []

    def lane_entry(lane: int) -> None:
        try:
            process_lane(lane)
        except Exception as error:
            stop.set()
            lane_errors.append(f"worker-{lane}:{type(error).__name__}:{error}")

    threads = [threading.Thread(target=lane_entry, args=(lane,), daemon=False)
               for lane in range(args.workers)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    for lane_lock in cache_locks:
        lane_lock.unlink(missing_ok=True)

    if lane_errors:
        latest_campaign: dict[str, dict[str, object]] = {}
        for event in load_attempt_events(attempt_path):
            if event.get("campaign_id") == campaign:
                latest_campaign[str(event.get("row_id"))] = event
        for row_id, event in latest_campaign.items():
            if event.get("status") == "RUNNING":
                blocked = dict(event)
                blocked.update({"status": "BLOCKED", "stage": "UNKNOWN",
                                "reason": "worker-exited-before-terminal-result"})
                append_event(blocked)
                terminal[row_id] = "BLOCKED"

    # Full frozen source authority is revalidated once at the epoch boundary.
    try:
        final_paths = source_paths(source_root)
        final_digest = hashlib.sha256()
        for rel in final_paths:
            final_digest.update(rel.encode("utf-8") + b"\0" + hash_file(source_root / Path(*rel.split("/"))).encode() + b"\n")
        source_unchanged = (final_paths == [str(row["canonical_source"]) for row in rows] and
                            final_digest.hexdigest() == unq(header["source_inventory_sha256"]))
    except (OSError, Refusal):
        source_unchanged = False
    try:
        alias_unchanged = hash_file(materialization) == unq(header["materialization_receipt_sha256"])
    except (OSError, Refusal):
        alias_unchanged = False
    try:
        for row in rows:
            physical, identity = file_identity(source_root / Path(*str(row["canonical_source"]).split("/")))
            if physical.casefold() != str(row["physical_source"]).casefold() or identity != row["physical_file_id"]:
                alias_unchanged = False
                break
    except (OSError, Refusal):
        alias_unchanged = False
    campaign_elapsed = int((time.monotonic() - start) * 1000)
    producer_end, runtime_end, tools_end, tool_id_end, env_id_end = safe_env_identity(
        env_base, producer, runtime, tools)
    try:
        helper_unchanged = hash_file(helper) == PINNED_BOUNDED_HELPER_SHA256
    except (OSError, Refusal):
        helper_unchanged = False
    integrity_ok = (source_unchanged and alias_unchanged and producer_end == producer_sha and
                    runtime_end == runtime_id and tools_end == tools_id and tool_id_end == tool_id and
                    env_id_end == env_id and helper_unchanged)
    if not integrity_ok:
        for row in rows:
            row_id = str(row["id"])
            if terminal.get(row_id) == "PASS":
                terminal[row_id] = "BLOCKED"
                append_event({"campaign_id": campaign, "row_id": row_id,
                              "canonical_source": row["canonical_source"],
                              "source_sha256": row["source_sha256"],
                              "source_snapshot_sha256": unq(header["source_inventory_sha256"]),
                              "alias_mapping_sha256": unq(header["alias_mapping_sha256"]),
                              "producer_sha256": producer_sha, "runtime_identity": runtime_id,
                              "tool_identity": tool_id, "environment_identity": env_id,
                              "target": TARGET, "backend": BACKEND,
                              "cache_owner": "campaign-boundary", "cache_root": str(cache_root),
                              "argv": [], "exit_code": None, "elapsed_ms": campaign_elapsed,
                              "peak_rss_kib": None, "stage": "UNKNOWN", "status": "BLOCKED",
                              "object_path": None, "object_bytes": None, "object_sha256": None,
                              "log_path": None, "reason": "campaign-authority-changed"})
    campaign_elapsed = int((time.monotonic() - start) * 1000)
    for row in rows:
        row_id = str(row["id"])
        terminal.setdefault(row_id, "PENDING")
    summary_counts = {status: sum(value == status for value in terminal.values()) for status in ALLOWED_STATUS}
    summary = [
        'schema: "object_campaign_summary_v1"', f"campaign_id: {q(campaign)}",
        f"inventory_sha256: {q(hash_file(inventory_path))}",
        f"inventory_count: {len(rows)}", f"elapsed_ms: {campaign_elapsed}",
        f"workers: {args.workers}", f"threads_per_worker: {args.threads}",
        f"max_rss_kib_per_worker: {args.max_rss_kib}",
        f"priority_manifest_sha256: {q(priority_manifest_sha256 or 'not-used')}",
        f"stop_requested: {'true' if stop_request_seen or stop_request_path.exists() else 'false'}",
        f"stop_request_path: {q(str(stop_request_path))}",
        f"source_unchanged: {'true' if source_unchanged else 'false'}",
        f"alias_mapping_unchanged: {'true' if alias_unchanged else 'false'}",
        f"producer_unchanged: {'true' if producer_end == producer_sha else 'false'}",
        f"runtime_unchanged: {'true' if runtime_end == runtime_id else 'false'}",
        f"toolchain_unchanged: {'true' if tools_end == tools_id else 'false'}",
        f"environment_unchanged: {'true' if env_id_end == env_id else 'false'}",
        f"bounded_helper_unchanged: {'true' if helper_unchanged else 'false'}",
    ]
    summary.extend(f"{status.lower()}_count: {summary_counts[status]}" for status in sorted(ALLOWED_STATUS))
    summary.append(f"worker_error_count: {len(lane_errors)}")
    for index, error in enumerate(lane_errors):
        summary.append(f"worker_error_{index}: {q(error)}")
    summary_path = work / "object_campaign_summary_v1.sdn"
    write_atomic(summary_path, "\n".join(summary) + "\n")
    # Do not remove stale locks automatically; owner must prove quiescence.
    lock_path.unlink()
    print(f"inventory_count={len(rows)}")
    print(f"pass={summary_counts['PASS']} failed={summary_counts['FAILED']} timeout={summary_counts['TIMEOUT']} unsupported={summary_counts['UNSUPPORTED']} blocked={summary_counts['BLOCKED']} pending={summary_counts['PENDING']}")
    print(f"attempts={attempt_path}")
    print(f"causes={cause_path}")
    print(f"summary={summary_path}")
    return 0 if integrity_ok and summary_counts["FAILED"] == 0 and summary_counts["TIMEOUT"] == 0 and summary_counts["BLOCKED"] == 0 and summary_counts["UNSUPPORTED"] == 0 and summary_counts["PENDING"] == 0 and not lane_errors else 1


def selftest() -> int:
    import tempfile
    with tempfile.TemporaryDirectory(prefix="windows-object-validator-") as temp:
        base = Path(temp)
        standard = base / "valid.obj"
        standard.write_bytes((0x8664).to_bytes(2, "little") + (1).to_bytes(2, "little") +
                             b"\0" * 12 + b"\0\0" + b"\0\0" + b"\0" * 40)
        size, kind = validate_amd64_coff(standard)
        assert size == 60 and kind == "COFF_AMD64"
        bigobj = base / "bigobj.obj"
        guid = bytes.fromhex("c7a1bad1eeba a94baf20faf66aa4dcb8".replace(" ", ""))
        header = b"\0\0\xff\xff" + (2).to_bytes(2, "little") + (0x8664).to_bytes(2, "little") + b"\0" * 4 + guid + b"\0" * 16 + (1).to_bytes(4, "little") + b"\0" * 8 + b"\0" * 40
        bigobj.write_bytes(header)
        _, kind = validate_amd64_coff(bigobj)
        assert kind == "COFF_BIGOBJ_AMD64"
        for name, payload in (("empty.obj", b""), ("pe.obj", b"MZ" + b"\0" * 80),
                              ("wrong-machine.obj", b"\x64\x86" + b"\0" * 58),
                              ("truncated.obj", b"\x64\x86\x01\0")):
            path = base / name
            path.write_bytes(payload)
            try:
                validate_amd64_coff(path)
            except Refusal:
                pass
            else:
                raise AssertionError("invalid COFF fixture was accepted: " + name)
    print("PASS: AMD64 COFF/BigObj structure and invalid output rejection")
    return 0


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    inventory = sub.add_parser("inventory", help="freeze canonical source roots and materialization aliases")
    inventory.add_argument("--source-root", type=Path, required=True)
    inventory.add_argument("--output-dir", type=Path, required=True)
    inventory.add_argument("--materialization-receipt", type=Path, required=True)
    campaign = sub.add_parser("collect", help="compile pending source rows to diagnostic AMD64 COFF objects")
    campaign.add_argument("--inventory", type=Path, required=True)
    campaign.add_argument("--source-root", type=Path, required=True)
    campaign.add_argument("--work-root", type=Path, required=True)
    campaign.add_argument("--cache-root", type=Path, required=True)
    campaign.add_argument("--producer", type=Path, required=True)
    campaign.add_argument("--runtime-capsule", type=Path, required=True)
    campaign.add_argument("--toolchain-dir", type=Path, required=True)
    campaign.add_argument("--priority-manifest", type=Path,
                          help="optional inventory-bound cohort to schedule before the full remainder")
    campaign.add_argument("--workers", type=int, default=2)
    campaign.add_argument("--threads", type=int, default=1)
    campaign.add_argument("--row-timeout-seconds", type=int, default=900)
    campaign.add_argument("--epoch-timeout-seconds", type=int, default=7200)
    campaign.add_argument("--max-rss-kib", type=int, default=6291456)
    sub.add_parser("selftest", help="validate synthetic COFF headers without invoking a compiler")
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        if args.command == "inventory":
            path = build_inventory(args.source_root, args.output_dir, args.materialization_receipt)
            _, rows = load_inventory(path)
            print(f"inventory={path}")
            print(f"row_count={len(rows)}")
            print(f"inventory_sha256={hash_file(path)}")
            return 0
        if args.command == "selftest":
            return selftest()
        if (args.workers, args.threads, args.row_timeout_seconds,
                args.epoch_timeout_seconds, args.max_rss_kib) != (2, 1, 900, 7200, 6291456):
            raise Refusal("campaign policy is fixed at 2 workers x 1 thread, 900s rows, 7200s epoch, 6291456 KiB/job")
        return collect(args)
    except (Refusal, OSError, subprocess.CalledProcessError, ValueError) as error:
        print(f"collect-windows-phase2-objects: BLOCKED: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
