#!/usr/bin/env python3
"""Fresh owned SQLCipher-compatible acceptance input; never a production writer.

Without --native, run the memory-only SQLite/crypto oracle. With --native,
create a private fresh directory, write encrypted inputs only, and pass a
CSPRNG-generated synthetic passphrase to the native child in its environment.
No plaintext database, passphrase receipt, or persistent key file is written.
The reference AES/SQLCipher helpers are NIST/hashlib anchored, but this is not
qualification against an independently installed SQLCipher implementation.
"""

import argparse
import ctypes
import hashlib
import importlib.util
import os
from pathlib import Path
import secrets
import sqlite3
import struct
import subprocess
import sys
import tempfile

if not __debug__:
    raise RuntimeError("This acceptance oracle requires Python assertions; omit -O.")

sys.dont_write_bytecode = True
REFERENCE = Path(__file__).resolve().parents[2] / "database/sqlcipher4/gen_sqlcipher4_fixture.py"
spec = importlib.util.spec_from_file_location("sqlcipher_reference", REFERENCE)
reference = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reference)  # Deliberately do not call reference.main().
PAGE = 4096
RESERVE = 80
USABLE = PAGE - RESERVE
SECRET_ENV = "SIMPLE_SECRET_MESSENGER_FRESH"
LONG_BODY = "overflow: 한글 ✓ " + "0123456789abcdef" * 700
UNICODE_BODY = 'unicode: 한글 héllo ✓ "quoted"\\path\nnext'
ROOMS = [(1, [None, "fresh general ✓", 1700000000]), (2, [None, "other room", 1700000100])]
MEMBERS = [(1, [None, 1, 101, 1700000001]), (2, [None, 1, 102, 1700000002]),
           (3, [None, 2, 103, 1700000003])]
MESSAGES = [(11, [None, 1, 101, "late-source-first", 1700000011, 30, None]),
            (12, [None, 1, 101, "tie-first", 1700000012, 10, None]),
            (13, [None, 1, 102, "tie-second", 1700000013, 10, None]),
            (14, [None, 1, 101, UNICODE_BODY, 1700000014, 20, None]),
            (15, [None, 1, 102, LONG_BODY, 1700000015, 50, None]),
            (16, [None, 2, 103, "other-room-only", 1700000016, 1, None])]
MESSAGES += [(i, [None, 2, 103, "filler-" + str(i) + "x" * 140, 1700000000 + i, i, None])
             for i in range(17, 57)]


def build_image(message_rows=None):
    """Small acceptance-only table/overflow builder with 4016-byte packing."""
    pages = {i: bytes(PAGE) for i in range(1, 5)}

    def allocate():
        number = len(pages) + 1
        pages[number] = bytes(PAGE)
        return number

    def leaf_cell(rowid, values):
        payload = reference.record(values)
        size = len(payload)
        minimum = ((USABLE - 12) * 32 // 255) - 23
        local = size
        if size > USABLE - 35:
            surplus = minimum + (size - minimum) % (USABLE - 4)
            local = surplus if surplus <= USABLE - 35 else minimum
        cell = reference.varint(size) + reference.varint(rowid) + payload[:local]
        if local != size:
            chunks = [payload[i:i + USABLE - 4] for i in range(local, size, USABLE - 4)]
            ids = [allocate() for _ in chunks]
            for index, chunk in enumerate(chunks):
                page = bytearray(PAGE)
                struct.pack_into(">I", page, 0, ids[index + 1] if index + 1 < len(ids) else 0)
                page[4:4 + len(chunk)] = chunk
                pages[ids[index]] = bytes(page)
            cell += struct.pack(">I", ids[0])
        return cell

    def pack(cells, kind, rightmost=0):
        page = bytearray(PAGE)
        header = 12 if kind == 5 else 8
        pointer = USABLE
        page[0] = kind
        struct.pack_into(">H", page, 3, len(cells))
        for index, cell in enumerate(cells):
            pointer -= len(cell)
            assert pointer >= header + 2 * len(cells)
            page[pointer:pointer + len(cell)] = cell
            struct.pack_into(">H", page, header + 2 * index, pointer)
        struct.pack_into(">H", page, 5, pointer)
        if kind == 5:
            struct.pack_into(">I", page, 8, rightmost)
        return bytes(page)

    schema = []
    for schema_id, (name, root, rows) in enumerate(
            [("room", 2, ROOMS), ("room_member", 3, MEMBERS), ("messages", 4, MESSAGES if message_rows is None else message_rows)], 1):
        groups = [[]]
        used = 8
        for rowid, values in rows:
            cell = leaf_cell(rowid, values)
            if used + len(cell) + 2 > USABLE:
                groups.append([])
                used = 8
            groups[-1].append((rowid, cell))
            used += len(cell) + 2
        if len(groups) == 1:
            pages[root] = pack([cell for _, cell in groups[0]], 13)
        else:
            children = [allocate() for _ in groups]
            for number, group in zip(children, groups):
                pages[number] = pack([cell for _, cell in group], 13)
            cells = [struct.pack(">I", number) + reference.varint(group[-1][0])
                     for number, group in zip(children[:-1], groups[:-1])]
            pages[root] = pack(cells, 5, children[-1])
        schema.append((schema_id, reference.record(["table", name, name, root, reference.SCHEMA_SQL[name]])))
    header = bytearray(reference.build_leaf(schema, base=100))
    header[:16] = b"SQLite format 3\x00"
    struct.pack_into(">H", header, 16, PAGE)
    header[18:24] = bytes([1, 1, RESERVE, 64, 32, 32])
    for offset, value in [(24, 1), (28, len(pages)), (40, 1), (44, 4), (56, 1), (92, 1), (96, 3050004)]:
        struct.pack_into(">I", header, offset, value)
    pages[1] = bytes(header)
    return b"".join(pages[i] for i in range(1, len(pages) + 1))


def sqlite_oracle(image):
    with sqlite3.connect(":memory:") as database:
        database.deserialize(image)
        assert database.execute("PRAGMA integrity_check").fetchall() == [("ok",)]
        for name, rows in [("room", ROOMS), ("room_member", MEMBERS), ("messages", MESSAGES)]:
            expected = [(rid, *values[1:]) for rid, values in rows]
            assert database.execute("SELECT * FROM " + name + " ORDER BY rowid").fetchall() == expected
        assert database.execute("SELECT id FROM messages WHERE room_id=1 ORDER BY seq,rowid LIMIT 3").fetchall() == [(12,), (13,), (14,)]


def encrypt_image(image, passphrase):
    salt = secrets.token_bytes(16)
    key, mac_key = reference.derive_keys(passphrase.encode("utf-8"), salt)
    encoded = bytearray()
    for page_no, offset in enumerate(range(0, len(image), PAGE), 1):
        body = image[offset:offset + USABLE]
        if page_no == 1:
            body = salt + body[16:]
        encoded += reference.encode_page(page_no, body, secrets.token_bytes(16), key, mac_key)
    rebuilt = bytearray()
    for page_no, offset in enumerate(range(0, len(encoded), PAGE), 1):
        rebuilt += reference.decode_page(page_no, encoded[offset:offset + PAGE], key, mac_key) + bytes(RESERVE)
    rebuilt[:16] = b"SQLite format 3\x00"
    assert bytes(rebuilt) == image
    sqlite_oracle(bytes(rebuilt))
    with sqlite3.connect(":memory:") as database:
        try:
            database.deserialize(bytes(encoded))
            database.execute("SELECT * FROM sqlite_schema").fetchall()
        except sqlite3.DatabaseError:
            pass
        else:
            raise AssertionError("plain SQLite accepted encrypted database")
    return bytes(encoded), key, mac_key


def private_directory(parent):
    if os.name != "nt":
        return Path(tempfile.mkdtemp(prefix="devhub-secured-", dir=parent))
    from ctypes import wintypes
    advapi = ctypes.WinDLL("advapi32", use_last_error=True)
    kernel = ctypes.WinDLL("kernel32", use_last_error=True)
    token = wintypes.HANDLE()
    kernel.GetCurrentProcess.restype = wintypes.HANDLE
    kernel.CloseHandle.argtypes = [wintypes.HANDLE]
    kernel.CloseHandle.restype = wintypes.BOOL
    kernel.LocalFree.argtypes = [ctypes.c_void_p]
    kernel.LocalFree.restype = ctypes.c_void_p
    advapi.OpenProcessToken.argtypes = [wintypes.HANDLE, wintypes.DWORD, ctypes.POINTER(wintypes.HANDLE)]
    advapi.OpenProcessToken.restype = wintypes.BOOL
    advapi.GetTokenInformation.argtypes = [wintypes.HANDLE, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(wintypes.DWORD)]
    advapi.GetTokenInformation.restype = wintypes.BOOL
    assert advapi.OpenProcessToken(kernel.GetCurrentProcess(), 8, ctypes.byref(token))
    try:
        needed = wintypes.DWORD()
        advapi.GetTokenInformation(token, 1, None, 0, ctypes.byref(needed))
        buffer = ctypes.create_string_buffer(needed.value)
        assert advapi.GetTokenInformation(token, 1, buffer, needed, ctypes.byref(needed))
        user_sid = ctypes.cast(buffer, ctypes.POINTER(ctypes.c_void_p))[0]
        sid_text = wintypes.LPWSTR()
        advapi.ConvertSidToStringSidW.argtypes = [ctypes.c_void_p, ctypes.POINTER(wintypes.LPWSTR)]
        assert advapi.ConvertSidToStringSidW(user_sid, ctypes.byref(sid_text))
        try:
            sddl = "D:P(A;OICI;FA;;;" + sid_text.value + ")(A;OICI;FA;;;SY)"
        finally:
            kernel.LocalFree(ctypes.cast(sid_text, ctypes.c_void_p))
    finally:
        kernel.CloseHandle(token)
    descriptor = ctypes.c_void_p()
    advapi.ConvertStringSecurityDescriptorToSecurityDescriptorW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, ctypes.POINTER(ctypes.c_void_p), ctypes.c_void_p]
    assert advapi.ConvertStringSecurityDescriptorToSecurityDescriptorW(sddl, 1, ctypes.byref(descriptor), None)

    class SecurityAttributes(ctypes.Structure):
        _fields_ = [("length", wintypes.DWORD), ("descriptor", ctypes.c_void_p), ("inherit", wintypes.BOOL)]

    attributes = SecurityAttributes(ctypes.sizeof(SecurityAttributes), descriptor, False)
    path = Path(parent).resolve() / ("devhub-secured-" + secrets.token_hex(12))
    kernel.CreateDirectoryW.argtypes = [wintypes.LPCWSTR, ctypes.POINTER(SecurityAttributes)]
    try:
        if not kernel.CreateDirectoryW(str(path), ctypes.byref(attributes)):
            raise ctypes.WinError(ctypes.get_last_error())
    finally:
        kernel.LocalFree(descriptor)
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path)
    parser.add_argument("--parent", type=Path, default=Path(tempfile.gettempdir()))
    args = parser.parse_args()
    reference.self_test_aes()
    image = build_image()
    sqlite_oracle(image)
    passphrase = secrets.token_urlsafe(32)
    encoded, key, mac_key = encrypt_image(image, passphrase)
    variants = {"fresh.sqlcipher4": encoded}
    for name, offset in [("tamper_first.sqlcipher4", 100), ("tamper_later.sqlcipher4", PAGE + 100)]:
        tampered = bytearray(encoded)
        tampered[offset] ^= 1
        variants[name] = bytes(tampered)
        page_no = offset // PAGE + 1
        try:
            reference.decode_page(page_no, tampered[(page_no - 1) * PAGE:page_no * PAGE], key, mac_key)
        except SystemExit:
            pass
        else:
            raise AssertionError("tampered oracle input authenticated")
    wrong_key, wrong_mac = reference.derive_keys(secrets.token_bytes(32), encoded[:16])
    try:
        reference.decode_page(1, encoded[:PAGE], wrong_key, wrong_mac)
    except SystemExit:
        pass
    else:
        raise AssertionError("wrong-key oracle input authenticated")
    invalid = bytearray(image)
    invalid[56:60] = struct.pack(">I", 4)  # Authenticated but unsupported SQLite text encoding.
    invalid_encoded, _, _ = encrypt_image_without_oracle(bytes(invalid), passphrase)
    variants["invalid_header.sqlcipher4"] = invalid_encoded
    malformed_rows = [(rowid, list(values)) for rowid, values in MESSAGES]
    malformed_rows[4][1][5] = "invalid-sequence-outside-limit"
    malformed_image = build_image(malformed_rows)
    with sqlite3.connect(":memory:") as database:
        database.deserialize(malformed_image)
        assert database.execute("PRAGMA integrity_check").fetchall() == [("ok",)]
        assert database.execute("SELECT typeof(seq) FROM messages WHERE id=15").fetchone() == ("text",)
    malformed_encoded, _, _ = encrypt_image_without_oracle(malformed_image, passphrase)
    variants["malformed_rows.sqlcipher4"] = malformed_encoded
    variants["short.bin"] = bytes(100)
    print("PASS fresh memory oracle: NIST AES, hashlib KDF/HMAC, SQLite integrity/rows/overflow, encrypted-input rejection")
    print("fixture pages=" + str(len(image) // PAGE) + " sha256=" + hashlib.sha256(encoded).hexdigest())
    if args.native is None:
        return 0
    native = args.native.resolve(strict=True)
    directory = private_directory(args.parent)
    hashes = {}
    for name, data in variants.items():
        path = directory / name
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_BINARY", 0), 0o600)
        with os.fdopen(descriptor, "wb") as output:
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        hashes[name] = hashlib.sha256(data).digest()
    before = {name: (os.stat(directory / name).st_size, os.stat(directory / name).st_mtime_ns,
                     os.stat(directory / name).st_mode) for name in variants}
    environment = dict(os.environ)
    environment[SECRET_ENV] = passphrase
    environment["DEVHUB_FRESH_DB_DIR"] = str(directory).replace("\\", "/")
    result = subprocess.run([str(native)], env=environment, timeout=180, check=False)
    for name in variants:
        path = directory / name
        stat = path.stat()
        assert hashlib.sha256(path.read_bytes()).digest() == hashes[name]
        assert (stat.st_size, stat.st_mtime_ns, stat.st_mode) == before[name]
    assert sorted(path.name for path in directory.iterdir()) == sorted(variants)
    print("PASS unchanged owned encrypted inputs and metadata; no plaintext/journal/secret files")
    print("private encrypted evidence=" + str(directory))
    return result.returncode


def encrypt_image_without_oracle(image, passphrase):
    """Authenticate a deliberately invalid header so header rejection is exercised."""
    salt = secrets.token_bytes(16)
    key, mac_key = reference.derive_keys(passphrase.encode("utf-8"), salt)
    pages = []
    for page_no, offset in enumerate(range(0, len(image), PAGE), 1):
        body = image[offset:offset + USABLE]
        if page_no == 1:
            body = salt + body[16:]
        pages.append(reference.encode_page(page_no, body, secrets.token_bytes(16), key, mac_key))
    return b"".join(pages), key, mac_key


if __name__ == "__main__":
    raise SystemExit(main())
