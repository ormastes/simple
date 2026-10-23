#!/usr/bin/env python3
"""Generate reference SQLite fixtures for std.nogc_sync_mut.database.sqlite_format specs.

Run from the repository root:

    python3 test/fixtures/database/sqlite/gen_fixtures.py

Emits:
  - messenger.sqlite    room/room_member/messages schema (plan section 6.5)
                        + type_probe table covering NULL/INTEGER/REAL/TEXT/BLOB
                        + a >1000-byte BLOB row that forces overflow pages.
  - walsample.sqlite    WAL-mode database (kept alongside its -wal frames).
  - ground_truth.json   machine-readable ground truth (page size, page count,
                        rootpages, schemas, rows) used to hardcode expected
                        values in the SSpec suites.

Everything is deterministic: fixed rowids, fixed timestamps, patterned BLOBs.
"""
import json
import os
import shutil
import sqlite3
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

SCHEMA_SQL = """
CREATE TABLE room (
  id INTEGER PRIMARY KEY,
  title TEXT NOT NULL,
  created_at INTEGER NOT NULL
);
CREATE TABLE room_member (
  id INTEGER PRIMARY KEY,
  room_id INTEGER NOT NULL,
  user_id INTEGER NOT NULL,
  joined_at INTEGER NOT NULL
);
CREATE TABLE messages (
  id INTEGER PRIMARY KEY,
  room_id INTEGER NOT NULL,
  sender_id INTEGER NOT NULL,
  body TEXT NOT NULL,
  created_at INTEGER NOT NULL,
  seq INTEGER NOT NULL,
  reply_to_id INTEGER
);
CREATE TABLE type_probe (
  id INTEGER PRIMARY KEY,
  n INTEGER,
  r REAL,
  t TEXT,
  b BLOB
);
""".strip()

# Deterministic patterned BLOB > maxLocal (usableSize - 35 = 4061 for 4096-byte
# pages) so the record is guaranteed to spill onto b-tree overflow pages.
BIG_BLOB = bytes(((i * 7 + 13) % 256) for i in range(5000))

ROOMS = [
    (1, "general", 1700000000),
    (2, "random", 1700000100),
]
ROOM_MEMBERS = [
    (1, 1, 101, 1700000001),
    (2, 1, 102, 1700000002),
    (3, 2, 102, 1700000101),
]
MESSAGES = [
    (1, 1, 101, "hello world", 1700000003, 1, None),
    (2, 1, 102, "hi there", 1700000004, 2, 1),
    (3, 1, 101, "unicode: héllo wörld ✓", 1700000005, 3, None),
    (4, 2, 102, "", 1700000102, 1, None),
]
# NULL / INTEGER (0, 1, negative, large) / REAL / TEXT (empty, unicode) / BLOB
# (empty, small, >1000-byte overflow) coverage.
TYPE_PROBES = [
    (1, 0, 0.0, "", b""),
    (2, 1, 1.5, "text", b"\x01\x02\x03"),
    (3, -1, -2.25, "héllo ✓", b"\xff\xfe\xfd\xfc"),
    (4, -9223372036854775808, -0.5, "x", b"\x00"),
    (5, 9223372036854775807, 3.141592653589793, "y", BIG_BLOB),
    (6, None, None, None, None),
]


def build_messenger(path: str) -> None:
    if os.path.exists(path):
        os.remove(path)
    conn = sqlite3.connect(path)
    try:
        conn.executescript(SCHEMA_SQL)
        conn.executemany(
            "INSERT INTO room (id, title, created_at) VALUES (?, ?, ?)", ROOMS
        )
        conn.executemany(
            "INSERT INTO room_member (id, room_id, user_id, joined_at) VALUES (?, ?, ?, ?)",
            ROOM_MEMBERS,
        )
        conn.executemany(
            "INSERT INTO messages (id, room_id, sender_id, body, created_at, seq, reply_to_id)"
            " VALUES (?, ?, ?, ?, ?, ?, ?)",
            MESSAGES,
        )
        conn.executemany(
            "INSERT INTO type_probe (id, n, r, t, b) VALUES (?, ?, ?, ?, ?)", TYPE_PROBES
        )
        conn.commit()
    finally:
        conn.close()


def build_wal_sample(db_path: str, wal_copy: str, db_copy: str) -> None:
    for p in (db_path, wal_copy, db_copy):
        if os.path.exists(p):
            os.remove(p)
    conn = sqlite3.connect(db_path)
    try:
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute("CREATE TABLE wal_t (id INTEGER PRIMARY KEY, v TEXT)")
        conn.executemany(
            "INSERT INTO wal_t (id, v) VALUES (?, ?)",
            [(1, "wal-one"), (2, "wal-two"), (3, "wal-three")],
        )
        conn.commit()
        # Copy main + wal while the connection is still open so the frames in
        # the -wal file survive as committed-but-not-checkpointed.
        shutil.copyfile(db_path, db_copy)
        shutil.copyfile(db_path + "-wal", wal_copy)
    finally:
        conn.close()


def read_text_encoding(conn) -> int:
    return conn.execute("PRAGMA encoding").fetchone()[0] and int(
        conn.execute("PRAGMA encoding").fetchone()[0]
    )


def ground_truth(db_path: str) -> dict:
    conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
    try:
        page_size = conn.execute("PRAGMA page_size").fetchone()[0]
        page_count = conn.execute("PRAGMA page_count").fetchone()[0]
        schema = conn.execute(
            "SELECT type, name, tbl_name, rootpage, sql FROM sqlite_schema"
            " WHERE name NOT LIKE 'sqlite_%' ORDER BY rowid"
        ).fetchall()
        tables = {}
        for obj_type, name, _tbl, rootpage, sql in schema:
            cols = [
                r[1] for r in conn.execute(f'PRAGMA table_info("{name}")').fetchall()
            ]
            rows = []
            if obj_type == "table":
                cur = conn.execute(f'SELECT * FROM "{name}" ORDER BY rowid')
                for row in cur.fetchall():
                    rows.append([_jsonable(v) for v in row])
            tables[name] = {
                "type": obj_type,
                "rootpage": rootpage,
                "columns": cols,
                "sql": sql,
                "rows": rows,
            }
        header = open(db_path, "rb").read(100)
        return {
            "page_size": page_size,
            "page_count": page_count,
            "text_encoding": int.from_bytes(header[56:60], "big"),
            "read_version": header[19],
            "write_version": header[18],
            "schema_cookie": int.from_bytes(header[40:44], "big"),
            "file_change_counter": int.from_bytes(header[24:28], "big"),
            "file_bytes": os.path.getsize(db_path),
            "sqlite_version": sqlite3.sqlite_version,
            "tables": tables,
        }
    finally:
        conn.close()


def _jsonable(v):
    if isinstance(v, bytes):
        return {"__blob__": list(v)}
    return v


def main() -> int:
    messenger = os.path.join(HERE, "messenger.sqlite")
    wal_db = os.path.join(HERE, "walsample.sqlite")
    wal_copy = os.path.join(HERE, "walsample-kept.sqlite-wal")
    db_copy = os.path.join(HERE, "walsample-kept.sqlite")

    build_messenger(messenger)
    build_wal_sample(wal_db, wal_copy, db_copy)

    truth = ground_truth(messenger)
    with open(os.path.join(HERE, "ground_truth.json"), "w", encoding="utf-8") as fh:
        json.dump(truth, fh, indent=2, ensure_ascii=False)

    print("sqlite module version:", sqlite3.sqlite_version)
    print("messenger:", truth["page_size"], "B pages x", truth["page_count"],
          "=", truth["file_bytes"], "B; encoding", truth["text_encoding"])
    for name, t in truth["tables"].items():
        print(f"  table {name}: rootpage={t['rootpage']} cols={t['columns']} rows={len(t['rows'])}")
    print("wal fixture:", db_copy, "+", wal_copy)
    return 0


if __name__ == "__main__":
    sys.exit(main())
