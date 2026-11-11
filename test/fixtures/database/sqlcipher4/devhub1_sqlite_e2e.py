#!/usr/bin/env python3
"""Lane devhub1 target-4 driver: real .sqlite -> encrypted -> devhub decrypt.

Steps (all with the repo's own tooling conventions):
  1. Create a REAL SQLite database with python's sqlite3 (the same tooling
     the repo's fixture generators use), with a known schema and known rows,
     and verify it with PRAGMA integrity_check.
  2. Re-lay the same schema+rows into the 4016-usable / 80-reserved page
     geometry the locked sqlcipher4_4k_sha512 profile decrypts to (the same
     technique as gen_sqlcipher4_fixture.build_plain_image), and verify the
     rebuilt image AGAIN with sqlite3.deserialize + exact row assertions.
  3. Encrypt the image with the specified algorithm via the repo's reference
     implementation (gen_sqlcipher4_fixture, NIST/hashlib anchored) under a
     fresh CSPRNG salt + passphrase, writing e2e.sqlcipher4 under
     build/interop/devhub1/e2e/ (gitignored).
  4. Print DEVHUB1_E2E_DIR / DEVHUB1_E2E_SECRET once (never persisted).

The spec side opens e2e.sqlcipher4 through the production devhub decrypt
path and asserts the sqlite header string, the page count, and a known row's
bytes in the decoded image (page-level assertions; row-cell VALUE text is
caret2's lane).
"""
import importlib.util
import os
import secrets
import sqlite3
import struct
import sys
from pathlib import Path

sys.dont_write_bytecode = True

REPO_ROOT = Path(__file__).resolve().parents[4]
REF_PATH = REPO_ROOT / "test/fixtures/database/sqlcipher4/gen_sqlcipher4_fixture.py"
spec = importlib.util.spec_from_file_location("sqlcipher_reference", REF_PATH)
reference = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reference)

PAGE = 4096
RESERVE = 80
USABLE = PAGE - RESERVE

SCHEMA = ("CREATE TABLE ledger (\n  id INTEGER PRIMARY KEY,\n  note TEXT NOT NULL,\n"
          "  amount REAL NOT NULL,\n  flag INTEGER NOT NULL,\n  payload BLOB NOT NULL\n)")
MARKER = "devhub1-e2e-marker-7f3a9c51"
ROWS = [
    (1, [None, "opening " + MARKER, 100.25, 1, bytes(range(16))]),
    (2, [None, "unicode héllo ✓ 한글", -55.5, 0, b"\xff\xfe\xfd\xfc\xfb\xfa\xf9\xf8"]),
    (3, [None, "third row", 0.0, 1, b""]),
]


def build_real_sqlite(path: Path) -> None:
    """A real .sqlite produced by the repo's sqlite tooling (python sqlite3)."""
    if path.exists():
        path.unlink()
    con = sqlite3.connect(str(path))
    try:
        con.execute("PRAGMA page_size=4096")
        con.execute("PRAGMA journal_mode=DELETE")
        con.execute(SCHEMA)
        for rowid, values in ROWS:
            con.execute(
                "INSERT INTO ledger (id, note, amount, flag, payload) VALUES (?,?,?,?,?)",
                (rowid, values[1], values[2], values[3], values[4]))
        con.commit()
        assert con.execute("PRAGMA integrity_check").fetchone()[0] == "ok"
        got = con.execute("SELECT id, note, amount, flag, payload FROM ledger ORDER BY id").fetchall()
        assert [list(r) for r in got] == [[r, *v[1:]] for r, v in ROWS]
    finally:
        con.close()


def build_profile_image() -> bytes:
    """The same schema+rows re-laid for 4016 usable bytes + 80 reserved."""
    cells = [(rid, reference.record(vals)) for rid, vals in ROWS]
    page2 = reference.build_leaf(cells, base=0)
    schema_cell = (1, reference.record(["table", "ledger", "ledger", 2, SCHEMA]))
    page1 = bytearray(reference.build_leaf([schema_cell], base=100))
    page1[0:16] = b"SQLite format 3\x00"
    struct.pack_into(">H", page1, 16, PAGE)
    page1[18] = 1
    page1[19] = 1
    page1[20] = RESERVE
    page1[21] = 64
    page1[22] = 32
    page1[23] = 32
    struct.pack_into(">I", page1, 24, 1)
    struct.pack_into(">I", page1, 28, 2)
    struct.pack_into(">I", page1, 40, 1)
    struct.pack_into(">I", page1, 44, 4)
    struct.pack_into(">I", page1, 56, 1)
    struct.pack_into(">I", page1, 92, 1)
    struct.pack_into(">I", page1, 96, 3050004)
    image = bytes(page1) + bytes(page2)
    # Oracle A again on the profile-layout image.
    con = sqlite3.connect(":memory:")
    try:
        con.deserialize(image)
        assert con.execute("PRAGMA integrity_check").fetchone()[0] == "ok"
        got = con.execute("SELECT id, note, amount, flag, payload FROM ledger ORDER BY id").fetchall()
        assert [list(r) for r in got] == [[r, *v[1:]] for r, v in ROWS]
    finally:
        con.close()
    return image


def encrypt_image(image: bytes, passphrase: str):
    salt = secrets.token_bytes(16)
    page_key, mac_key = reference.derive_keys(passphrase.encode("utf-8"), salt)
    out = bytearray()
    for page_no, off in enumerate(range(0, len(image), PAGE), 1):
        body = image[off:off + USABLE]
        if page_no == 1:
            body = salt + body[16:]
        iv = secrets.token_bytes(16)
        out += reference.encode_page(page_no, body, iv, page_key, mac_key)
    return bytes(out), salt, page_key, mac_key


def main() -> int:
    reference.self_test_aes()
    out_dir = REPO_ROOT / "build/interop/devhub1/e2e"
    out_dir.mkdir(parents=True, exist_ok=True)
    real_path = out_dir / "real.sqlite"
    build_real_sqlite(real_path)
    image = build_profile_image()
    passphrase = secrets.token_urlsafe(24)
    encoded, salt, page_key, mac_key = encrypt_image(image, passphrase)
    # Reference round-trip check on the emitted file.
    rebuilt = bytearray()
    for page_no, off in enumerate(range(0, len(encoded), PAGE), 1):
        page = encoded[off:off + PAGE]
        body = reference.decode_page(page_no, page, page_key, mac_key)
        rebuilt += body + b"\x00" * RESERVE
    rebuilt[0:16] = b"SQLite format 3\x00"
    assert bytes(rebuilt) == image, "reference round-trip mismatch"
    (out_dir / "e2e.sqlcipher4").write_bytes(encoded)
    (out_dir / "manifest.sdn").write_text(
        "# devhub1 sqlite e2e manifest (non-secret).\n"
        "dir: {dir}\n"
        "db_file: e2e.sqlcipher4\n"
        "page_count: 2\n"
        "rows: 3\n"
        "marker: {marker}\n"
        "real_sqlite: real.sqlite\n".format(dir=str(out_dir).replace("\\", "/"), marker=MARKER),
        encoding="utf-8")
    print("DEVHUB1_E2E_DIR={}".format(str(out_dir).replace("\\", "/")))
    print("DEVHUB1_E2E_SECRET={}".format(passphrase))
    print("devhub1 sqlite e2e: real.sqlite={} bytes encrypted={} bytes".format(
        real_path.stat().st_size, len(encoded)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
