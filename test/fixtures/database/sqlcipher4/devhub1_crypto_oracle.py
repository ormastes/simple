#!/usr/bin/env python3
"""Lane devhub1 OSS interop oracle — the specified SQLCipher 4 algorithm
implemented with the Python `cryptography` package (provisioned by
scripts/deps/provision-interop-crypto.shs; OpenSSL-backed CPython stdlib is
not used here, this module is the `cryptography` oracle).

Implements EXACTLY the locked sqlcipher4_4k_sha512 profile:
    page_key  = PBKDF2-HMAC-SHA512(passphrase, file_salt, 256000, 32)
    hmac_salt = each file_salt byte XOR 0x3a
    hmac_key  = PBKDF2-HMAC-SHA512(page_key, hmac_salt, 2, 32)
    page      = [salt?] || AES-256-CBC-no-padding(body) || IV(16) || HMAC-SHA512
    per-page HMAC input = ciphertext || IV || page_number_le32 (1-based)

Modes:
    oss-encrypt   read pt_page_<n>.bin (4016-byte virtual bodies, n = 1..page
                  count from page_count.txt) + DEVHUB1_PASSPHRASE; fresh CSPRNG
                  salt; write salt.bin + enc_page_<n>.bin (4096 bytes each).
                  Page 1 stores the salt at [0,16) (caller convention of the
                  profile, matching provision.py and gen_sqlcipher4_fixture).
    oss-decrypt   read salt.bin + enc_page_<n>.bin + pt_page_<n>.bin;
                  authenticate BEFORE decrypt (HMAC verify, fail-closed);
                  compare plaintext byte-for-byte; write verdict.txt.

Env: DEVHUB1_VEC_DIR (vector directory), DEVHUB1_PASSPHRASE (secret bytes as
UTF-8 text; only ever an environment value, never written).

Exit codes: 0 success; 3 authentication failure (oss-decrypt); 4 mismatch;
5 usage/IO error.
"""
import os
import secrets
import struct
import sys
from pathlib import Path

from cryptography.hazmat.primitives import hashes, hmac
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

PAGE = 4096
BODY = 4016
KDF_ITER = 256000
HMAC_KDF_ITER = 2
HMAC_MASK = 0x3A


def derive_keys(passphrase: bytes, salt: bytes):
    page_key = PBKDF2HMAC(hashes.SHA512(), 32, salt, KDF_ITER).derive(passphrase)
    hmac_salt = bytes(b ^ HMAC_MASK for b in salt)
    hmac_key = PBKDF2HMAC(hashes.SHA512(), 32, hmac_salt, HMAC_KDF_ITER).derive(page_key)
    return page_key, hmac_key


def page_hmac(hmac_key: bytes, ciphertext: bytes, iv: bytes, page_no: int) -> bytes:
    signer = hmac.HMAC(hmac_key, hashes.SHA512())
    signer.update(ciphertext)
    signer.update(iv)
    signer.update(struct.pack("<I", page_no))
    return signer.finalize()


def encrypt_page(page_no: int, body: bytes, iv: bytes, salt: bytes,
                 page_key: bytes, hmac_key: bytes) -> bytes:
    assert len(body) == BODY
    if page_no == 1:
        stored_head, pt = salt, body[16:]
    else:
        stored_head, pt = b"", body
    cipher = Cipher(algorithms.AES(page_key), modes.CBC(iv))
    enc = cipher.encryptor()
    ct = enc.update(pt) + enc.finalize()
    mac = page_hmac(hmac_key, ct, iv, page_no)
    return stored_head + ct + iv + mac


def decrypt_page(page_no: int, page: bytes, page_key: bytes, hmac_key: bytes) -> bytes:
    assert len(page) == PAGE
    ct_off = 16 if page_no == 1 else 0
    ct = page[ct_off:ct_off + BODY - ct_off]
    iv = page[PAGE - 80:PAGE - 64]
    mac = page[PAGE - 64:]
    # AUTHENTICATE BEFORE DECRYPT — mirrors the pure-Simple codec contract.
    signer = hmac.HMAC(hmac_key, hashes.SHA512())
    signer.update(ct)
    signer.update(iv)
    signer.update(struct.pack("<I", page_no))
    signer.verify(mac)  # raises InvalidSignature on mismatch
    cipher = Cipher(algorithms.AES(page_key), modes.CBC(iv))
    dec = cipher.decryptor()
    pt = dec.update(ct) + dec.finalize()
    if page_no == 1:
        return page[:16] + pt
    return pt


def vec_dir() -> Path:
    d = os.environ.get("DEVHUB1_VEC_DIR")
    if not d:
        raise SystemExit("DEVHUB1_VEC_DIR is not set")
    return Path(d)


def passphrase() -> bytes:
    p = os.environ.get("DEVHUB1_PASSPHRASE")
    if p is None or p == "":
        raise SystemExit("DEVHUB1_PASSPHRASE is not set")
    return p.encode("utf-8")


def page_count(d: Path) -> int:
    return int((d / "page_count.txt").read_text(encoding="ascii").strip())


def cmd_encrypt(d: Path) -> int:
    pp = passphrase()
    salt = secrets.token_bytes(16)
    page_key, hmac_key = derive_keys(pp, salt)
    n_pages = page_count(d)
    (d / "salt.bin").write_bytes(salt)
    for n in range(1, n_pages + 1):
        body = bytes.fromhex((d / "pt_page_{}.hex".format(n)).read_text(encoding="ascii").strip())
        iv = secrets.token_bytes(16)
        (d / "enc_page_{}.bin".format(n)).write_bytes(
            encrypt_page(n, body, iv, salt, page_key, hmac_key))
    print("OSS_ENCRYPT_OK pages={} salt_len={}".format(n_pages, len(salt)))
    return 0


def cmd_decrypt(d: Path) -> int:
    pp = passphrase()
    salt = bytes.fromhex((d / "salt.hex").read_text(encoding="ascii").strip())
    page_key, hmac_key = derive_keys(pp, salt)
    n_pages = page_count(d)
    lines = []
    failed = False
    for n in range(1, n_pages + 1):
        page = (d / "enc_page_{}.bin".format(n)).read_bytes()
        expected = bytes.fromhex((d / "pt_page_{}.hex".format(n)).read_text(encoding="ascii").strip())
        try:
            pt = decrypt_page(n, page, page_key, hmac_key)
        except Exception as auth_error:
            print("OSS_DECRYPT_AUTH_FAIL page={}: {}".format(n, auth_error))
            return 3
        if n == 1:
            # Caller convention: the encrypted page 1 stores the salt at
            # [0,16), replacing the body's head (provision.py and
            # gen_sqlcipher4_fixture do the same).
            expected = salt + expected[16:]
        if pt != expected:
            print("OSS_DECRYPT_MISMATCH page={} got={} want={}".format(n, len(pt), len(expected)))
            lines.append("MISMATCH {}".format(n))
            failed = True
        else:
            lines.append("MATCH {}".format(n))
    (d / "verdict.txt").write_text("\n".join(lines) + "\n", encoding="ascii")
    print("OSS_DECRYPT_OK pages={}".format(n_pages))
    return 4 if failed else 0


def main() -> int:
    if len(sys.argv) != 2 or sys.argv[1] not in ("oss-encrypt", "oss-decrypt"):
        print("usage: devhub1_crypto_oracle.py oss-encrypt|oss-decrypt", file=sys.stderr)
        return 5
    d = vec_dir()
    if not d.is_dir():
        print("vector dir missing: {}".format(d), file=sys.stderr)
        return 5
    try:
        if sys.argv[1] == "oss-encrypt":
            return cmd_encrypt(d)
        return cmd_decrypt(d)
    except (OSError, ValueError, AssertionError) as error:
        print("oracle IO/geometry error: {}".format(error), file=sys.stderr)
        return 5


if __name__ == "__main__":
    raise SystemExit(main())
