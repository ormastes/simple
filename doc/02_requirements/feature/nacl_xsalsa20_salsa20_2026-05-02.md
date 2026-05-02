# FR: NACL crypto_box / crypto_secretbox (XSalsa20-Poly1305 + X25519)

**Filed:** 2026-05-02
**Track:** Crypto / NACL public-key authenticated encryption
**Sibling FRs:** `argon2_native_runtime_helpers_2026-05-02.md`, `scrypt_native_runtime_helpers_2026-05-02.md`

## Problem

DJB's NaCl library defines `crypto_box` and `crypto_secretbox` — high-level
authenticated encryption that composes X25519 key agreement, HSalsa20 key
derivation, XSalsa20 stream encryption, and Poly1305 MAC.

The following pieces are already present in pure Simple:

| Primitive | Location | Status |
|-----------|----------|--------|
| X25519 key exchange | `src/os/crypto/curve25519.spl` | Present (`x25519`, `x25519_base`) |
| Poly1305 MAC | `src/os/crypto/poly1305.spl` | Present (`poly1305_mac`) |
| Salsa20/8 quarterround (scrypt internal) | `src/lib/common/scrypt/salsa20.spl` | Present — reference only; round count differs from Salsa20/20 |

The following pieces are **absent** and block implementation:

| Primitive | Notes |
|-----------|-------|
| **Salsa20/20** | Full 20-round stream cipher; `src/lib/common/scrypt/salsa20.spl` implements only the 8-round scrypt core and has no nonce-driven streaming API |
| **HSalsa20** | 20-round Salsa20 evaluated at a 16-byte sub-key derivation input; needed to reduce a 24-byte XSalsa20 nonce to a 32-byte ChaCha/Salsa sub-key |
| **XSalsa20** | Salsa20 with a 24-byte nonce via HSalsa20 derivation (DJB, "Extending the Salsa20 nonce", 2011) |

Until Salsa20/20 + HSalsa20 + XSalsa20 exist as reusable modules in
`src/os/crypto/`, the NACL wrappers cannot be written without embedding
an unchecked Salsa20/20 inline — a cover-up pattern prohibited by
`feedback_no_coverups.md`.

## Requested Public API

New file: `src/os/crypto/nacl.spl`

```
# Symmetric authenticated encryption (XSalsa20-Poly1305)
fn crypto_secretbox(message: [u8], nonce: [u8] /* 24B */, key: [u8] /* 32B */) -> [u8]
fn crypto_secretbox_open(ciphertext: [u8], nonce: [u8], key: [u8]) -> Result<[u8], text>

# Public-key authenticated encryption (X25519 + HSalsa20 + XSalsa20-Poly1305)
fn crypto_box(message: [u8], nonce: [u8] /* 24B */, recipient_pk: [u8] /* 32B */, sender_sk: [u8] /* 32B */) -> [u8]
fn crypto_box_open(ciphertext: [u8], nonce: [u8], recipient_sk: [u8], sender_pk: [u8]) -> Result<[u8], text>
fn crypto_box_keypair() -> ([u8], [u8])   # (public_key, secret_key)
```

## Dependency Chain

Implementation order:

1. `src/os/crypto/salsa20.spl` — Salsa20/20 stream cipher (quarterround from scrypt salsa20 is a reference; must be reimplemented for 20 rounds with full nonce/counter streaming API)
2. `src/os/crypto/hsalsa20.spl` (or inline in salsa20.spl) — HSalsa20 sub-key derivation
3. `src/os/crypto/xsalsa20.spl` (or inline) — XSalsa20 stream with 24-byte nonce via HSalsa20
4. `src/os/crypto/nacl.spl` — NACL wrappers composing X25519 + HSalsa20 + XSalsa20 + Poly1305

## Acceptance Criteria

- All four files above exist as pure Simple (no externs, no FFI).
- KAT spec at `test/unit/os/crypto/nacl_kat_spec.spl` passes byte-exact for:
  - At least 1 `crypto_secretbox` round-trip against NACL official test vectors
    (https://nacl.cr.yp.to/secretbox.html)
  - At least 1 `crypto_box` round-trip against NACL official test vectors
    (https://nacl.cr.yp.to/box.html)
  - At least 1 tamper-rejection case (flipped ciphertext byte → `Err`)
- `crypto_box_keypair()` produces a valid X25519 key pair (verified via
  round-trip: `crypto_box` with `(pk_b, sk_a)` decrypts with `(sk_b, pk_a)`).
- Constant-time tag comparison in `crypto_secretbox_open` / `crypto_box_open`
  (same pattern as `src/os/crypto/chacha20_poly1305.spl`).

## References

- DJB, "Salsa20 specification" (2005) — https://cr.yp.to/snuffle/spec.pdf
- DJB, "Extending the Salsa20 nonce" (2011) — https://cr.yp.to/snuffle/xsalsa-20110204.pdf
- NaCl `crypto_secretbox` test vectors — https://nacl.cr.yp.to/secretbox.html
- NaCl `crypto_box` test vectors — https://nacl.cr.yp.to/box.html
- RFC 7748 (X25519 / Curve25519) — reuse `src/os/crypto/curve25519.spl`
