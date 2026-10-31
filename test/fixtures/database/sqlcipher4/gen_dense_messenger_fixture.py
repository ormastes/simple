#!/usr/bin/env python3
"""Deterministic public copy of the DevHub Messenger multi-page encrypted database.

The system fixture (test/fixtures/devhub/fresh_secured_db/provision.py) builds a
9-page SQLCipher-4 database with an ephemeral secret.  This script reuses its
builders (build_image, sqlite_oracle, encrypt_image) with a PUBLIC synthetic test
passphrase, a fixed salt and fixed per-page IVs, so the SAME content is
committed as test data for the integration and acceptance layers.

THE PASSPHRASE BELOW IS PUBLIC TEST DATA.  It protects nothing and must never be
reused for anything real.

Every expected value in dense_ground_truth.json comes from Python's sqlite3 on
the plaintext image, from hashlib, or from json.dumps -- never from the code
under test.

Run from anywhere:  python gen_dense_messenger_fixture.py
"""

import hashlib
import importlib.util
import json
import os
import sqlite3
import struct
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
PROVISION = os.path.join(HERE, "..", "..", "devhub", "fresh_secured_db", "provision.py")
spec = importlib.util.spec_from_file_location("provision", PROVISION)
provision = importlib.util.module_from_spec(spec)
spec.loader.exec_module(provision)  # main() is guarded; nothing runs on import.
reference = provision.reference

PASSPHRASE = "public-test-passphrase-not-a-secret"
SALT = bytes(range(0xA0, 0xB0))
SECRET_REF = "secret://messenger/dense"
ENV_VAR = "SIMPLE_SECRET_MESSENGER_DENSE"
PAGE = provision.PAGE
RESERVE = provision.RESERVE
USABLE = provision.USABLE
PREFIX = "dense_multipage"


def iv_fn(page_no):
    return reference.page_iv(page_no)


def varint_decode(data, pos):
    value = 0
    for index in range(9):
        byte = data[pos + index]
        if index == 8:
            return (value << 8) | byte, index + 1
        value = (value << 7) | (byte & 0x7F)
        if not byte & 0x80:
            return value, index + 1


def overflow_geometry(image):
    """Locate the message-15 cell's overflow pointer by parsing the plaintext image."""
    for page_no in range(1, len(image) // PAGE + 1):
        base = (page_no - 1) * PAGE
        page = image[base:base + PAGE]
        if page_no == 1 or page[0] != 13:
            continue
        count = struct.unpack_from(">H", page, 3)[0]
        pointers = sorted(struct.unpack_from(">H", page, 8 + 2 * i)[0] for i in range(count))
        for pointer in pointers:
            size, n1 = varint_decode(page, pointer)
            rowid, n2 = varint_decode(page, pointer + n1)
            if rowid != 15:
                continue
            later = [p for p in pointers if p > pointer]
            end = later[0] if later else USABLE
            pointer_offset = end - 4
            first = struct.unpack_from(">I", page, pointer_offset)[0]
            chain = []
            current = first
            while current:
                chain.append(current)
                current = struct.unpack_from(">I", image, (current - 1) * PAGE)[0]
            return {"leaf_page": page_no, "pointer_offset_in_page": pointer_offset,
                    "pointer_image_offset": base + pointer_offset, "first_overflow_page": first,
                    "overflow_chain": chain, "record_size": size,
                    "chain_next_image_offsets": [(p - 1) * PAGE for p in chain]}
    raise AssertionError("overflow cell for message 15 not found")


def jstr(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


def message_object(row):
    mid, room_id, sender_id, body, created_at, seq = row[0], row[1], row[2], row[3], row[4], row[5]
    return ("{\"id\":" + jstr(str(mid)) + ",\"room_id\":" + jstr(str(room_id)) +
            ",\"sender_id\":" + jstr(str(sender_id)) + ",\"created_at\":" + jstr(str(created_at)) +
            ",\"seq\":" + jstr(str(seq)) + ",\"body\":" + jstr(body) + "}")


def cell_text(value):
    return "NULL" if value is None else str(value)


def main():
    reference.self_test_aes()
    image = provision.build_image()
    provision.sqlite_oracle(image)
    encoded, key, mac_key = provision.encrypt_image(image, PASSPHRASE, SALT, iv_fn)
    again, _, _ = provision.encrypt_image(image, PASSPHRASE, SALT, iv_fn)
    assert encoded == again, "generator must be deterministic"
    page_count = len(image) // PAGE
    assert page_count == 9 and len(encoded) == len(image)

    # Ground truth: python sqlite3 over the plaintext image.
    tables = {}
    with sqlite3.connect(":memory:") as database:
        database.deserialize(image)
        for name in ["room", "room_member", "messages"]:
            columns = [c[1] for c in database.execute("PRAGMA table_info(" + name + ")")]
            rows = database.execute("SELECT * FROM " + name + " ORDER BY rowid").fetchall()
            tables[name] = {"columns": columns, "rows": rows}
        order = {}
        for room in (1, 2):
            order[str(room)] = [r[0] for r in database.execute(
                "SELECT id FROM messages WHERE room_id=? ORDER BY seq, rowid", (room,))]
        members_by_room = {str(room): [r for r in tables["room_member"]["rows"] if r[1] == room] for room in (1, 2)}
    messages = {row[0]: row for row in tables["messages"]["rows"]}
    overflow_body = messages[15][3]
    unit = "0123456789abcdef"
    head = "overflow: 한글 ✓ "
    assert overflow_body == head + unit * 700 and len(overflow_body.encode("utf-8")) > 11000
    assert order["1"] == [12, 13, 14, 11, 15], order["1"]
    assert messages[12][5] == messages[13][5], "equal sequence values are the point"

    geometry = overflow_geometry(image)
    # The pointer must really be the on-disk overflow link: sqlite3 reads the body through it.
    assert struct.unpack_from(">I", image, geometry["pointer_image_offset"])[0] == geometry["first_overflow_page"]
    assert len(geometry["overflow_chain"]) >= 2

    # Expected product payloads, serialised by json.dumps (not by the Simple code).
    rooms_payload = "{\"rooms\":[" + ",".join(
        "{\"id\":" + jstr(str(r[0])) + ",\"name\":" + jstr(r[1]) + "}" for r in tables["room"]["rows"]) + \
        "],\"count\":" + str(len(tables["room"]["rows"])) + "}"
    members_payload = {}
    for room, rows in members_by_room.items():
        members_payload[room] = "{\"members\":[" + ",".join(
            "{\"room_id\":" + jstr(str(r[1])) + ",\"identity_id\":" + jstr(str(r[2])) +
            ",\"joined_at\":" + jstr(str(r[3])) + "}" for r in rows) + "],\"count\":" + str(len(rows)) + "}"
    objects = {str(mid): message_object(row) for mid, row in messages.items() if mid != 15}
    full15 = message_object(messages[15])
    cut = full15.index(unit)
    suffix_len = len("\"}")
    assert full15 == full15[:cut] + unit * 700 + full15[len(full15) - suffix_len:]
    overflow = {"row_id": 15, "body_utf8_bytes": len(overflow_body.encode("utf-8")),
                "body_sha256": hashlib.sha256(overflow_body.encode("utf-8")).hexdigest(),
                "unit": unit, "repeat": 700,
                "object_head": full15[:cut], "object_tail": full15[len(full15) - suffix_len:],
                "payload_utf8_bytes": len(full15.encode("utf-8")), **geometry}

    # Committed encrypted files.
    files = {}

    def emit(name, data):
        with open(os.path.join(HERE, name), "wb") as handle:
            handle.write(data)
        files[name] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}

    base = PREFIX + ".sqlcipher4"
    emit(base, encoded)
    for name, offset in [(PREFIX + "_tamper_first.sqlcipher4", 100), (PREFIX + "_tamper_later.sqlcipher4", PAGE + 100)]:
        tampered = bytearray(encoded)
        tampered[offset] ^= 1
        page_no = offset // PAGE + 1
        try:
            reference.decode_page(page_no, bytes(tampered[(page_no - 1) * PAGE:page_no * PAGE]), key, mac_key)
        except SystemExit:
            pass
        else:
            raise AssertionError("tampered oracle input authenticated")
        emit(name, bytes(tampered))
    invalid = bytearray(image)
    invalid[56:60] = struct.pack(">I", 4)  # authenticated but unsupported text encoding
    emit(PREFIX + "_invalid_header.sqlcipher4",
         provision.encrypt_image_without_oracle(bytes(invalid), PASSPHRASE, SALT, iv_fn)[0])
    malformed = [(rowid, list(values)) for rowid, values in provision.MESSAGES]
    malformed[4][1][5] = "invalid-sequence-outside-limit"
    malformed_image = provision.build_image(malformed)
    with sqlite3.connect(":memory:") as database:
        database.deserialize(malformed_image)
        assert database.execute("PRAGMA integrity_check").fetchall() == [("ok",)]
        assert database.execute("SELECT typeof(seq) FROM messages WHERE id=15").fetchone() == ("text",)
    emit(PREFIX + "_malformed_rows.sqlcipher4",
         provision.encrypt_image_without_oracle(malformed_image, PASSPHRASE, SALT, iv_fn)[0])
    # Structurally damaged FILES (no key material needed to build them).
    emit(PREFIX + "_truncated_4_pages.sqlcipher4", encoded[:4 * PAGE])
    emit(PREFIX + "_partial_page.dat", encoded[:PAGE + 123])
    emit(PREFIX + "_empty.dat", b"")

    truth = {
        "_notice": "PUBLIC SYNTHETIC TEST DATA. The passphrase protects nothing; never reuse it.",
        "generator": "test/fixtures/database/sqlcipher4/gen_dense_messenger_fixture.py",
        "passphrase": PASSPHRASE, "secret_ref": SECRET_REF, "env_var": ENV_VAR,
        "salt_hex": SALT.hex(), "page_size": PAGE, "page_count": page_count,
        "reserved_bytes": RESERVE, "text_encoding": 1, "file_bytes": len(encoded),
        "layout": {"iv_offset": USABLE, "hmac_offset": USABLE + 16, "first_page_ciphertext_offset": 16,
                   "later_page_ciphertext_offset": 0},
        "files": files,
        "tables": {name: {"columns": t["columns"],
                          "rows": [[cell_text(c) if not (name == "messages" and r[0] == 15 and i == 3) else "<overflow>"
                                    for i, c in enumerate(r)] for r in t["rows"]]}
                   for name, t in tables.items()},
        "overflow": overflow,
        "history_order": {room: ids for room, ids in order.items()},
        "message_object": objects,
        "rooms_payload": rooms_payload,
        "members_payload": members_payload,
        "missing_message_payload": "{\"found\":false,\"id\":\"999999\"}",
        "unicode_message_id": 14,
        "escaped_body_json": jstr(messages[14][3]),
    }
    with open(os.path.join(HERE, "dense_ground_truth.json"), "w", encoding="utf-8", newline="\n") as handle:
        json.dump(truth, handle, indent=1, ensure_ascii=False)
        handle.write("\n")
    for name, info in files.items():
        print(name, info["bytes"], info["sha256"])
    print("overflow chain", geometry["overflow_chain"], "pointer@", geometry["pointer_image_offset"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
