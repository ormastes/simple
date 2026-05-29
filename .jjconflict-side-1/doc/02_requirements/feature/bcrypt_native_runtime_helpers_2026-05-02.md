# FR: bcrypt Native Runtime Helpers (Eksblowfish Fast Path)

**Filed:** 2026-05-02
**Track:** Crypto / password-hashing native fast path
**Sibling FRs:** `argon2_native_runtime_helpers_2026-05-02.md`, `scrypt_native_runtime_helpers_2026-05-02.md`

## Problem

The pure-Simple bcrypt implementation at `src/os/crypto/bcrypt.spl` follows
Provos & Mazières 1999 byte-for-byte (Eksblowfish key setup, 16-round Blowfish
encrypt, $2a$ Modular Crypt Format output), but Eksblowfish is deliberately
CPU-intensive: cost=4 requires 2^4 = 16 outer iterations, each running
`ExpandKey` which touches the 18-entry P-array and 4×256 S-boxes through
~512 Blowfish encryptions. Total per hash: ~33 000 Blowfish encryptions.

Under the Simple interpreter (`bin/simple <spec.spl>`) this blows past the
60 s test-runner watchdog for cost=4. The `bcrypt_kat_spec.spl` spec therefore
parks the full jBCrypt byte-exact KAT vectors behind `pending(...)` until a
native fast path (or substantially faster compiled-mode interpreter) lands.

## Acceptance Criteria

- A native runtime helper (or compiled-mode acceleration) for the Eksblowfish
  inner loop — specifically `_bf_expand_key` and `_bf_encrypt` — that reduces
  a cost=4 hash to O(milliseconds) rather than O(minutes).
- `bcrypt_kat_spec.spl` upgrades its `pending` blocks to full byte-exact
  `expect(_bytes_to_hex(...)).to_equal(...)` assertions against jBCrypt
  test_vectors (BCryptTest.java):
  - vector 1: empty pw, salt "ZjIzMjE0", cost=4
    expected `$2a$04$ZjIzMjE0/RWPtJ3BDSWKWehnhrR8e.0.S.R6Xp5B8ynxE1pKLHzp.`
  - vector 2: pw "password", same salt, cost=4
    expected `$2a$04$ZjIzMjE0/RWPtJ3BDSWKW.4/16.rPtMoTWBg6iEMrPGa7jCfaAj..`
  - (additional jBCrypt vectors per BCryptTest.java)
- No new untrusted FFI: helper lives in the existing native runtime shim or
  is provided by compiled-mode acceleration.

## Cross-Reference

- Pure-Simple impl: `src/os/crypto/bcrypt.spl`
- Spec: `test/unit/lib/crypto/bcrypt_kat_spec.spl`
- Sibling pattern: `src/os/crypto/argon2.spl` + `argon2_native_runtime_helpers_2026-05-02.md`
- jBCrypt source: https://github.com/jeremyh/jBCrypt
