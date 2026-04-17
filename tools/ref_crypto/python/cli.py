#!/usr/bin/env python3
# Reference crypto CLI — Python cryptography library.
# Invoked by test/support/crypto_ref_harness.spl via rt_process_run.
# Uniform argv contract: <prim> <hex_args...>. Stdout: lowercase hex. Exit 0 on success.

import sys
import binascii

def _err(msg):
    sys.stderr.write(f"ref_python: {msg}\n")
    sys.exit(2)

def _hx(s):
    try:
        return binascii.unhexlify(s) if s else b""
    except binascii.Error as e:
        _err(f"bad hex: {e}")

def _out(b):
    sys.stdout.write(binascii.hexlify(b).decode() + "\n")

def main(argv):
    if len(argv) < 2:
        _err("usage: cli.py <primitive> <args...>")
    prim = argv[1]
    a = argv[2:]

    if prim == "sha256":
        from cryptography.hazmat.primitives import hashes
        h = hashes.Hash(hashes.SHA256()); h.update(_hx(a[0])); _out(h.finalize())
    elif prim == "sha512":
        from cryptography.hazmat.primitives import hashes
        h = hashes.Hash(hashes.SHA512()); h.update(_hx(a[0])); _out(h.finalize())
    elif prim == "hmac_sha256":
        from cryptography.hazmat.primitives import hashes, hmac
        h = hmac.HMAC(_hx(a[0]), hashes.SHA256()); h.update(_hx(a[1])); _out(h.finalize())
    elif prim == "hmac_sha512":
        from cryptography.hazmat.primitives import hashes, hmac
        h = hmac.HMAC(_hx(a[0]), hashes.SHA512()); h.update(_hx(a[1])); _out(h.finalize())
    elif prim == "hkdf_sha256":
        from cryptography.hazmat.primitives import hashes
        from cryptography.hazmat.primitives.kdf.hkdf import HKDF
        salt, ikm, info, length = _hx(a[0]), _hx(a[1]), _hx(a[2]), int(a[3])
        k = HKDF(algorithm=hashes.SHA256(), length=length, salt=salt, info=info).derive(ikm)
        _out(k)
    elif prim == "pbkdf2_sha256":
        from cryptography.hazmat.primitives import hashes
        from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
        pw, salt, iters, length = _hx(a[0]), _hx(a[1]), int(a[2]), int(a[3])
        k = PBKDF2HMAC(algorithm=hashes.SHA256(), length=length, salt=salt, iterations=iters).derive(pw)
        _out(k)
    elif prim in ("aes_128_gcm_encrypt", "aes_256_gcm_encrypt"):
        from cryptography.hazmat.primitives.ciphers.aead import AESGCM
        key, nonce, aad, plain = _hx(a[0]), _hx(a[1]), _hx(a[2]), _hx(a[3])
        expected_key_len = 16 if prim == "aes_128_gcm_encrypt" else 32
        if len(key) != expected_key_len:
            _err(f"key length mismatch: got {len(key)} want {expected_key_len}")
        ct = AESGCM(key).encrypt(nonce, plain, aad if aad else None)
        # Output: cipher_hex || tag_hex (tag is last 16 bytes of ct)
        _out(ct)
    elif prim == "chacha20":
        from cryptography.hazmat.primitives.ciphers import Cipher, algorithms
        key, nonce, counter, plain = _hx(a[0]), _hx(a[1]), int(a[2]), _hx(a[3])
        # cryptography wants full_nonce = counter(LE 4B) || iv(12B) — only exposes 16-byte nonce API
        if len(nonce) != 12:
            _err("chacha20 nonce must be 12 bytes")
        full_nonce = counter.to_bytes(4, "little") + nonce
        enc = Cipher(algorithms.ChaCha20(key, full_nonce), mode=None).encryptor()
        _out(enc.update(plain) + enc.finalize())
    elif prim == "poly1305":
        from cryptography.hazmat.primitives import poly1305 as p1305
        p = p1305.Poly1305(_hx(a[0])); p.update(_hx(a[1])); _out(p.finalize())
    elif prim == "chacha20_poly1305_encrypt":
        from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
        key, nonce, aad, plain = _hx(a[0]), _hx(a[1]), _hx(a[2]), _hx(a[3])
        _out(ChaCha20Poly1305(key).encrypt(nonce, plain, aad if aad else None))
    elif prim == "x25519":
        from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey
        scalar, peer = _hx(a[0]), _hx(a[1])
        sk = X25519PrivateKey.from_private_bytes(scalar)
        pk = X25519PublicKey.from_public_bytes(peer)
        _out(sk.exchange(pk))
    elif prim == "ed25519_sign":
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
        sk, msg = _hx(a[0]), _hx(a[1])
        _out(Ed25519PrivateKey.from_private_bytes(sk).sign(msg))
    elif prim == "ed25519_verify":
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
        from cryptography.exceptions import InvalidSignature
        pk, msg, sig = _hx(a[0]), _hx(a[1]), _hx(a[2])
        try:
            Ed25519PublicKey.from_public_bytes(pk).verify(sig, msg)
            sys.stdout.write("1\n")
        except InvalidSignature:
            sys.stdout.write("0\n")
    else:
        _err(f"unsupported primitive: {prim}")

if __name__ == "__main__":
    main(sys.argv)
