#!/usr/bin/env python3
"""Lane devhub1 fresh-provisioning driver: real encrypted inputs, CSPRNG secret.

Reuses the repo's own provision tooling (test/fixtures/devhub/fresh_secured_db/
provision.py — caret1's acceptance oracle, which chains the NIST/hashlib-
anchored reference) to build a fresh messenger image and encrypt it with a
CSPRNG passphrase. Writes ONLY encrypted inputs plus a non-secret SDN
manifest under build/review/ (gitignored, like provision.py's private
directory). The passphrase is printed to stdout as
DEVHUB1_FRESH_SECRET=<value> exactly once and is never persisted; the caller
(exports it into the spec run environment, mirroring provision.py --native).

encrypt_image() runs the reference round-trip + sqlite oracles before any
byte is emitted, so a broken generator fails here, not in the spec.

Usage:
    python3 test/fixtures/database/sqlcipher4/devhub1_provision_fresh.py
"""
import hashlib
import importlib.util
import secrets
import sys
from pathlib import Path

sys.dont_write_bytecode = True

REPO_ROOT = Path(__file__).resolve().parents[4]
PROVISION = REPO_ROOT / "test/fixtures/devhub/fresh_secured_db/provision.py"

spec = importlib.util.spec_from_file_location("devhub_fresh_provision", PROVISION)
provision = importlib.util.module_from_spec(spec)
spec.loader.exec_module(provision)  # defines build_image/encrypt_image; main() not called

PAGE = 4096


def main() -> int:
    out_dir = REPO_ROOT / "build/review/p3fix-devhub1-20261111-fresh"
    out_dir.mkdir(parents=True, exist_ok=True)

    image = provision.build_image()
    passphrase = secrets.token_urlsafe(32)
    encoded, key, mac_key = provision.encrypt_image(image, passphrase)

    fresh_path = out_dir / "fresh.sqlcipher4"
    fresh_path.write_bytes(encoded)

    tampered = bytearray(encoded)
    tampered[100] ^= 1
    (out_dir / "tamper_first.sqlcipher4").write_bytes(bytes(tampered))
    # Reference oracle must reject the tampered page before we ship it.
    try:
        provision.reference.decode_page(1, bytes(tampered[:PAGE]), key, mac_key)
    except SystemExit:
        pass
    else:
        raise AssertionError("tampered driver input authenticated in the oracle")

    short_path = out_dir / "short.bin"
    short_path.write_bytes(bytes(100))

    manifest = out_dir / "manifest.sdn"
    manifest.write_text(
        "# devhub1 fresh-provisioning manifest (non-secret).\n"
        "dir: {dir}\n"
        "fresh_file: fresh.sqlcipher4\n"
        "tamper_file: tamper_first.sqlcipher4\n"
        "short_file: short.bin\n"
        "page_count: {pages}\n"
        "file_bytes: {nbytes}\n"
        "fresh_sha256: {sha}\n"
        "image_sha256: {isha}\n".format(
            dir=str(out_dir).replace("\\", "/"),
            pages=len(encoded) // PAGE,
            nbytes=len(encoded),
            sha=hashlib.sha256(encoded).hexdigest(),
            isha=hashlib.sha256(image).hexdigest()),
        encoding="utf-8")

    print("DEVHUB1_FRESH_DIR={}".format(str(out_dir).replace("\\", "/")))
    print("DEVHUB1_FRESH_SECRET={}".format(passphrase))
    print("devhub1 fresh provisioning: pages={} sha256={}".format(
        len(encoded) // PAGE, hashlib.sha256(encoded).hexdigest()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
