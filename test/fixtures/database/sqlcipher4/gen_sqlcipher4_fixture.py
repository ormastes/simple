#!/usr/bin/env python3
"""Generate the SQLCipher-4 messenger fixture for the storage-port /
devhub-adapter integration specs.

Run from the repository root:

    python3 test/fixtures/database/sqlcipher4/gen_sqlcipher4_fixture.py

The environment has no sqlcipher binary / pysqlcipher3 / AES package, so
this generator implements the two primitives it needs in pure python:

  * AES-256 block encrypt/decrypt (self-checked against the NIST SP 800-38A
    F.2.5 CBC-AES256 known-answer vector before any fixture byte is
    emitted), used CBC with no padding;
  * a minimal, deterministic SQLite v3 image builder (single-leaf table
    b-trees, no overflow rows) laid out for page_size=4096 with
    reserved_bytes=80 — the geometry the locked sqlcipher4_4k_sha512
    profile decrypts to.

Independence record (verification/SSpec owner rule: pinned reference
tools, no roundtrip-only claims):
  * ORACLE A  — python's own sqlite3 opens the PLAINTEXT image:
                integrity_check == 'ok' and exact row assertions.
  * ORACLE B  — python decrypts the emitted SQLCipher-4 file with the
                locked profile (PBKDF2-HMAC-SHA512 256000 iters via
                hashlib, HMAC-SHA512 per page via hmac), re-opens the
                reconstructed image with sqlite3, asserts the same rows.
  * The Simple side re-asserts in spec: right passphrase decodes + real
    content, wrong passphrase fails HMAC with zero plaintext released
    (cipher lanes already anchored AES/HMAC/PBKDF2 against NIST/hashlib
    goldens).

Emits (deterministic: fixed salt, fixed IVs, fixed rows):
  - messenger.sqlcipher4        the encrypted fixture database
  - messenger_tampered.sqlcipher4  same file with one ciphertext byte of
                              page 2 flipped (HMAC authentication vector)
  - not_page_multiple.bin     100 zero bytes (geometry rejection vector)
  - messenger_plain.sqlite    the plaintext pre-encryption image (oracle aid)
  - ground_truth.json         page facts, table rows, salt, fixture passphrase
"""

import hashlib
import hmac as hmac_mod
import json
import os
import struct
import sqlite3
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

PAGE_SIZE = 4096
RESERVED = 80
USABLE = PAGE_SIZE - RESERVED
SQLITE_VERSION_NUMBER = 3050004

FIXTURE_PASSPHRASE = "messenger-fixture-passphrase"
FILE_SALT = bytes(range(0x30, 0x40))  # 16 fixed bytes, deterministic fixture

KDF_ITER = 256000
HMAC_KDF_ITER = 2
HMAC_SALT_MASK = 0x3A

# Deterministic per-page IVs (fixture only; production IVs are CSPRNG draws
# per encoded page — the codec contract, owned by the caller's rng).
def page_iv(page_no: int) -> bytes:
    return bytes([(page_no * 17 + i) & 0xFF for i in range(16)])

# ---------------------------------------------------------------------------
# Minimal AES-256 (encrypt + decrypt block), validated against NIST.
# ---------------------------------------------------------------------------

_SBOX = [
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,
    0x76,0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,
    0x72,0xc0,0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,
    0xd8,0x31,0x15,0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,
    0xeb,0x27,0xb2,0x75,0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,
    0xb3,0x29,0xe3,0x2f,0x84,0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,
    0xbe,0x39,0x4a,0x4c,0x58,0xcf,0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,
    0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,
    0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,
    0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,0x60,0x81,0x4f,0xdc,0x22,0x2a,
    0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,0xe0,0x32,0x3a,0x0a,0x49,
    0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,0xe7,0xc8,0x37,0x6d,
    0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,0xba,0x78,0x25,
    0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,0x70,0x3e,
    0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,0xe1,
    0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,
    0x16,
]
_SBOX = _SBOX[:256]
_INV_SBOX = [0] * 256
for _i, _v in enumerate(_SBOX):
    _INV_SBOX[_v] = _i
assert len(_SBOX) == 256 and len(set(_SBOX)) == 256

RCON = [0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1B,0x36,0x6C,0xD8,0xAB,0x4D]


def _xtime(a):
    a <<= 1
    if a & 0x100:
        a ^= 0x11B
    return a & 0xFF


def _mul(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        a = _xtime(a)
        b >>= 1
    return out


def _expand_key(key32: bytes):
    assert len(key32) == 32
    words = [list(key32[i:i + 4]) for i in range(0, 32, 4)]
    for i in range(8, 60):
        temp = list(words[i - 1])
        if i % 8 == 0:
            temp = temp[1:] + temp[:1]
            temp = [_SBOX[b] for b in temp]
            temp[0] ^= RCON[i // 8 - 1]
        elif i % 8 == 4:
            temp = [_SBOX[b] for b in temp]
        words.append([words[i - 8][j] ^ temp[j] for j in range(4)])
    return words


def _add_round_key(state, words, rnd):
    for c in range(4):
        w = words[rnd * 4 + c]
        for r in range(4):
            state[r][c] ^= w[r]


def _sub_bytes(state, box):
    for r in range(4):
        for c in range(4):
            state[r][c] = box[state[r][c]]


def _shift_rows(state):
    for r in range(1, 4):
        state[r] = state[r][r:] + state[r][:r]


def _inv_shift_rows(state):
    for r in range(1, 4):
        state[r] = state[r][-r:] + state[r][:-r]


def _mix_columns(state):
    for c in range(4):
        a0, a1, a2, a3 = (state[r][c] for r in range(4))
        state[0][c] = _xtime(a0) ^ (_xtime(a1) ^ a1) ^ a2 ^ a3
        state[1][c] = a0 ^ _xtime(a1) ^ (_xtime(a2) ^ a2) ^ a3
        state[2][c] = a0 ^ a1 ^ _xtime(a2) ^ (_xtime(a3) ^ a3)
        state[3][c] = (_xtime(a0) ^ a0) ^ a1 ^ a2 ^ _xtime(a3)


def _inv_mix_columns(state):
    for c in range(4):
        a0, a1, a2, a3 = (state[r][c] for r in range(4))
        state[0][c] = _mul(a0,14)^_mul(a1,11)^_mul(a2,13)^_mul(a3,9)
        state[1][c] = _mul(a0,9)^_mul(a1,14)^_mul(a2,11)^_mul(a3,13)
        state[2][c] = _mul(a0,13)^_mul(a1,9)^_mul(a2,14)^_mul(a3,11)
        state[3][c] = _mul(a0,11)^_mul(a1,13)^_mul(a2,9)^_mul(a3,14)


def aes256_encrypt_block(words, block16: bytes) -> bytes:
    state = [[block16[r + 4 * c] for c in range(4)] for r in range(4)]
    _add_round_key(state, words, 0)
    for rnd in range(1, 14):
        _sub_bytes(state, _SBOX)
        _shift_rows(state)
        _mix_columns(state)
        _add_round_key(state, words, rnd)
    _sub_bytes(state, _SBOX)
    _shift_rows(state)
    _add_round_key(state, words, 14)
    return bytes(state[r][c] for c in range(4) for r in range(4))


def aes256_decrypt_block(words, block16: bytes) -> bytes:
    state = [[block16[r + 4 * c] for c in range(4)] for r in range(4)]
    _add_round_key(state, words, 14)
    for rnd in range(13, 0, -1):
        _inv_shift_rows(state)
        _sub_bytes(state, _INV_SBOX)
        _add_round_key(state, words, rnd)
        _inv_mix_columns(state)
    _inv_shift_rows(state)
    _sub_bytes(state, _INV_SBOX)
    _add_round_key(state, words, 0)
    return bytes(state[r][c] for c in range(4) for r in range(4))


def self_test_aes():
    """NIST SP 800-38A F.2.5 CBC-AES256 known-answer check (both directions,
    all four published blocks chained)."""
    key = bytes.fromhex(
        "603deb1015ca71be2b73aef0857d7781"
        "1f352c073b6108d72d9810a30914dff4")
    iv = bytes.fromhex("000102030405060708090a0b0c0d0e0f")
    pts = [
        "6bc1bee22e409f96e93d7e117393172a",
        "ae2d8a571e03ac9c9eb76fac45af8e51",
        "30c81c46a35ce411e5fbc1191a0a52ef",
        "f69f2445df4f9b17ad2b417be66c3710",
    ]
    cts = [
        "f58c4c04d6e5f1ba779eabfb5f7bfbd6",
        "9cfc4e967edb808d679f777bc6702c7d",
        "39f23369a9d9bacfa530e26304231461",
        "b2eb05e2c39be9fcda6c19078c6a9d1b",
    ]
    # Constants verified against openssl enc -aes-256-cbc with the NIST
    # F.2.5 key/IV/plaintext above (pinned independent tool on this host).
    words = _expand_key(key)
    prev = iv
    for pt, ct in zip(pts, cts):
        block = bytes(a ^ b for a, b in zip(bytes.fromhex(pt), prev))
        enc = aes256_encrypt_block(words, block)
        assert enc.hex() == ct, f"AES KAT encrypt mismatch: {enc.hex()} != {ct}"
        dec = aes256_decrypt_block(words, enc)
        assert dec == block, "AES KAT decrypt mismatch"
        prev = enc
    print("AES self-test: NIST SP 800-38A F.2.5 CBC-AES256 ok (4 blocks, both directions)")


# ---------------------------------------------------------------------------
# SQLCipher 4 page codec (locked profile sqlcipher4_4k_sha512).
# ---------------------------------------------------------------------------

def derive_keys(passphrase: bytes, file_salt: bytes):
    page_key = hashlib.pbkdf2_hmac("sha512", passphrase, file_salt, KDF_ITER, 32)
    hmac_salt = bytes(b ^ HMAC_SALT_MASK for b in file_salt)
    hmac_key = hashlib.pbkdf2_hmac("sha512", page_key, hmac_salt, HMAC_KDF_ITER, 32)
    return page_key, hmac_key


def encode_page(page_no: int, body: bytes, iv: bytes, page_key: bytes, hmac_key: bytes) -> bytes:
    """body: the 4016-byte virtual page body (page 1: salt||plaintext[16:])."""
    assert len(body) == USABLE
    words = _expand_key(page_key)
    if page_no == 1:
        stored_head, pt = body[:16], body[16:]
    else:
        stored_head, pt = b"", body
    assert len(pt) % 16 == 0
    ct = b""
    prev = iv
    for off in range(0, len(pt), 16):
        block = bytes(a ^ b for a, b in zip(pt[off:off + 16], prev))
        enc = aes256_encrypt_block(words, block)
        ct += enc
        prev = enc
    mac = hmac_mod.new(hmac_key, ct + iv + struct.pack("<I", page_no), hashlib.sha512).digest()
    if page_no == 1:
        return stored_head + ct + iv + mac
    return ct + iv + mac


def decode_page(page_no: int, page: bytes, page_key: bytes, hmac_key: bytes) -> bytes:
    assert len(page) == PAGE_SIZE
    ct_off = 16 if page_no == 1 else 0
    ct_len = PAGE_SIZE - RESERVED - ct_off
    ct = page[ct_off:ct_off + ct_len]
    iv = page[PAGE_SIZE - RESERVED:PAGE_SIZE - RESERVED + 16]
    mac = page[PAGE_SIZE - 64:]
    expect = hmac_mod.new(hmac_key, ct + iv + struct.pack("<I", page_no), hashlib.sha512).digest()
    if not hmac_mod.compare_digest(expect, mac):
        raise SystemExit(f"page {page_no} HMAC mismatch during generator oracle")
    words = _expand_key(page_key)
    pt = b""
    prev = iv
    for off in range(0, len(ct), 16):
        dec = aes256_decrypt_block(words, ct[off:off + 16])
        pt += bytes(a ^ b for a, b in zip(dec, prev))
        prev = ct[off:off + 16]
    if page_no == 1:
        return page[:16] + pt
    return pt


# ---------------------------------------------------------------------------
# Minimal SQLite v3 image builder (single-leaf rowid tables, no overflow).
# ---------------------------------------------------------------------------

def varint(n: int) -> bytes:
    if n < 0:
        n += 1 << 64
    if n < 0x80:
        return bytes([n])
    out = bytearray()
    while n:
        out.insert(0, n & 0x7F)
        n >>= 7
    for i in range(len(out) - 1):
        out[i] |= 0x80
    return bytes(out)


def record(vals) -> bytes:
    serials = []
    bodies = []
    for v in vals:
        if v is None:
            serials.append(0)
            bodies.append(b"")
        elif isinstance(v, int):
            size = 1
            while not (-(1 << (size * 8 - 1)) <= v < (1 << (size * 8 - 1))):
                size += 1
                if size == 6:
                    break
            serials.append(size)
            bodies.append(v.to_bytes(size, "big", signed=True))
        elif isinstance(v, float):
            serials.append(7)
            bodies.append(struct.pack(">d", v))
        elif isinstance(v, str):
            raw = v.encode("utf-8")
            serials.append(13 + 2 * len(raw))
            bodies.append(raw)
        elif isinstance(v, bytes):
            serials.append(12 + 2 * len(v))
            bodies.append(v)
        else:
            raise TypeError(v)
    hdr = b""
    for s in serials:
        hdr += varint(s)
    hlen = len(hdr) + 1
    assert hlen < 0x80
    return varint(hlen) + hdr + b"".join(bodies)


def build_leaf(cells, base: int) -> bytes:
    """cells: list of (rowid, payload), ascending rowid. Layout within the
    usable region [0, USABLE); header displacement `base` (100 on page 1)."""
    page = bytearray(PAGE_SIZE)
    ptr = USABLE
    ptrs = []
    for rowid, payload in cells:
        cell = varint(len(payload)) + varint(rowid) + payload
        ptr -= len(cell)
        assert ptr >= base + 8 + 2 * len(cells), "cell content exceeded usable region"
        page[ptr:ptr + len(cell)] = cell
        ptrs.append(ptr)
    page[base] = 0x0D
    struct.pack_into(">H", page, base + 3, len(cells))
    struct.pack_into(">H", page, base + 5, ptr if cells else 0)
    for i, p in enumerate(ptrs):
        struct.pack_into(">H", page, base + 8 + 2 * i, p)
    return bytes(page)


SCHEMA_SQL = {
    "room": ("CREATE TABLE room (\n  id INTEGER PRIMARY KEY,\n  title TEXT NOT NULL,\n"
             "  created_at INTEGER NOT NULL\n)"),
    "room_member": ("CREATE TABLE room_member (\n  id INTEGER PRIMARY KEY,\n  room_id INTEGER NOT NULL,\n"
                    "  user_id INTEGER NOT NULL,\n  joined_at INTEGER NOT NULL\n)"),
    "messages": ("CREATE TABLE messages (\n  id INTEGER PRIMARY KEY,\n  room_id INTEGER NOT NULL,\n"
                 "  sender_id INTEGER NOT NULL,\n  body TEXT NOT NULL,\n  created_at INTEGER NOT NULL,\n"
                 "  seq INTEGER NOT NULL,\n  reply_to_id INTEGER\n)"),
    "type_probe": ("CREATE TABLE type_probe (\n  id INTEGER PRIMARY KEY,\n  n INTEGER,\n  r REAL,\n"
                   "  t TEXT,\n  b BLOB\n)"),
}

# (table name, rootpage, rows). IPK columns are stored as NULL placeholders;
# the rowid is the key (reader fills the IPK column from the b-tree key).
TABLES = [
    ("room", 2, [
        (1, [None, "general", 1700000000]),
        (2, [None, "random", 1700000100]),
    ]),
    ("room_member", 3, [
        (1, [None, 1, 101, 1700000001]),
        (2, [None, 1, 102, 1700000002]),
        (3, [None, 2, 102, 1700000101]),
    ]),
    ("messages", 4, [
        (1, [None, 1, 101, "hello world", 1700000003, 1, None]),
        (2, [None, 1, 102, "hi there", 1700000004, 2, 1]),
        (3, [None, 1, 101, "unicode: héllo wörld ✓", 1700000005, 3, None]),
        (4, [None, 2, 102, "second room says hi", 1700000102, 1, None]),
    ]),
    ("type_probe", 5, [
        (1, [None, 0, 0.0, "", b""]),
        (2, [None, 1, 1.5, "text", b"\x01\x02\x03"]),
        (3, [None, -1, -2.25, "héllo ✓", b"\xff\xfe\xfd\xfc"]),
    ]),
]


def build_plain_image() -> bytes:
    pages = {}
    schema_cells = []
    for idx, (name, rootpage, rows) in enumerate(TABLES):
        cells = [(rid, record(vals)) for rid, vals in rows]
        pages[rootpage] = build_leaf(cells, base=0)
        schema_cells.append((idx + 1, record(["table", name, name, rootpage, SCHEMA_SQL[name]])))
    page1 = bytearray(build_leaf(schema_cells, base=100))
    page_count = 1 + len(TABLES)
    # 100-byte database header.
    page1[0:16] = b"SQLite format 3\x00"
    struct.pack_into(">H", page1, 16, PAGE_SIZE)
    page1[18] = 1  # write version: legacy
    page1[19] = 1  # read version: legacy
    page1[20] = RESERVED
    page1[21] = 64
    page1[22] = 32
    page1[23] = 32
    struct.pack_into(">I", page1, 24, 1)            # change counter
    struct.pack_into(">I", page1, 28, page_count)   # db size in pages
    struct.pack_into(">I", page1, 40, 1)            # schema cookie
    struct.pack_into(">I", page1, 44, 4)            # schema format
    struct.pack_into(">I", page1, 56, 1)            # UTF-8
    struct.pack_into(">I", page1, 92, 1)            # version-valid-for
    struct.pack_into(">I", page1, 96, SQLITE_VERSION_NUMBER)
    pages[1] = bytes(page1)
    image = b"".join(pages[i] for i in range(1, page_count + 1))
    assert len(image) == page_count * PAGE_SIZE
    return image


# ---------------------------------------------------------------------------
# Oracles
# ---------------------------------------------------------------------------

EXPECTED_ROWS = {
    "room": [[1, "general", 1700000000], [2, "random", 1700000100]],
    "room_member": [[1, 1, 101, 1700000001], [2, 1, 102, 1700000002], [3, 2, 102, 1700000101]],
    "messages": [[1, 1, 101, "hello world", 1700000003, 1, None],
                 [2, 1, 102, "hi there", 1700000004, 2, 1],
                 [3, 1, 101, "unicode: héllo wörld ✓", 1700000005, 3, None],
                 [4, 2, 102, "second room says hi", 1700000102, 1, None]],
    "type_probe": [[1, 0, 0.0, "", b""], [2, 1, 1.5, "text", b"\x01\x02\x03"],
                   [3, -1, -2.25, "héllo ✓", b"\xff\xfe\xfd\xfc"]],
}


def oracle_open(image: bytes, label: str):
    path = os.path.join(HERE, "_oracle_tmp.sqlite")
    with open(path, "wb") as f:
        f.write(image)
    try:
        con = sqlite3.connect(path)
        try:
            ic = con.execute("PRAGMA integrity_check").fetchone()[0]
            assert ic == "ok", f"{label}: integrity_check={ic}"
            for table, expected in EXPECTED_ROWS.items():
                cols = [r[1] for r in con.execute(f"PRAGMA table_info({table})")]
                got = con.execute(f"SELECT {', '.join(cols)} FROM {table} ORDER BY id").fetchall()
                got = [list(r) for r in got]
                assert got == [list(r) for r in expected], f"{label}: {table} rows mismatch:\n{got}\n!=\n{expected}"
            print(f"oracle {label}: sqlite3 integrity ok + exact rows for {len(EXPECTED_ROWS)} tables")
        finally:
            con.close()
    finally:
        os.unlink(path)


def main():
    self_test_aes()

    image = build_plain_image()
    page_count = len(image) // PAGE_SIZE
    oracle_open(image, "A (plaintext layout)")

    passphrase = FIXTURE_PASSPHRASE.encode("utf-8")
    page_key, hmac_key = derive_keys(passphrase, FILE_SALT)

    encrypted = bytearray()
    for pg in range(1, page_count + 1):
        body = image[(pg - 1) * PAGE_SIZE:(pg - 1) * PAGE_SIZE + USABLE]
        if pg == 1:
            body = FILE_SALT + body[16:]
        encrypted += encode_page(pg, body, page_iv(pg), page_key, hmac_key)
    assert len(encrypted) == page_count * PAGE_SIZE

    plain_path = os.path.join(HERE, "messenger_plain.sqlite")
    with open(plain_path, "wb") as f:
        f.write(image)
    enc_path = os.path.join(HERE, "messenger.sqlcipher4")
    with open(enc_path, "wb") as f:
        f.write(encrypted)

    # Deterministic adversarial vectors for the storage-port spec:
    #  * one ciphertext byte inside page 2 flipped (must fail per-page HMAC)
    #  * a 100-byte file (not a whole number of 4096-byte pages)
    tampered = bytearray(encrypted)
    tampered[4200] ^= 0x01
    tampered_path = os.path.join(HERE, "messenger_tampered.sqlcipher4")
    with open(tampered_path, "wb") as f:
        f.write(tampered)
    short_path = os.path.join(HERE, "not_page_multiple.bin")
    with open(short_path, "wb") as f:
        f.write(b"\x00" * 100)

    # Oracle B: decrypt the emitted file, re-open with sqlite3.
    rebuilt = bytearray()
    for pg in range(1, page_count + 1):
        page = encrypted[(pg - 1) * PAGE_SIZE:pg * PAGE_SIZE]
        body = decode_page(pg, page, page_key, hmac_key)
        rebuilt += body + b"\x00" * RESERVED
    # Page 1: virtual [0,16) is the salt; the SQLite magic overlays it.
    rebuilt[0:16] = b"SQLite format 3\x00"
    oracle_open(bytes(rebuilt), "B (decrypted sqlcipher4)")

    ground_truth = {
        "profile": "sqlcipher4_4k_sha512",
        "page_size": PAGE_SIZE,
        "page_count": page_count,
        "reserved_bytes": RESERVED,
        "text_encoding": 1,
        "file_bytes": page_count * PAGE_SIZE,
        "salt_hex": FILE_SALT.hex(),
        "fixture_passphrase": FIXTURE_PASSPHRASE,
        "secret_ref": "secret://messenger/fixture",
        "env_var": "SIMPLE_SECRET_MESSENGER_FIXTURE",
        "tables": {
            name: {
                "rootpage": rootpage,
                "sql": SCHEMA_SQL[name],
                "rows": [[("blob", list(b)) if isinstance(b, bytes) else b for b in row] for _rid, row in rows],
            }
            for name, rootpage, rows in TABLES
        },
    }
    gt_path = os.path.join(HERE, "ground_truth.json")
    with open(gt_path, "w", encoding="utf-8") as f:
        json.dump(ground_truth, f, indent=1, ensure_ascii=False)

    print(f"wrote {enc_path} ({len(encrypted)} bytes, {page_count} pages)")
    print(f"wrote {tampered_path} (page-2 ciphertext byte flipped)")
    print(f"wrote {short_path} (100 bytes)")
    print(f"wrote {plain_path} ({len(image)} bytes)")
    print(f"wrote {gt_path}")


if __name__ == "__main__":
    sys.exit(main())
