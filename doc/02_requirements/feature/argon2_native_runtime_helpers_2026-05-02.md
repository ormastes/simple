# FR: Argon2id Native Runtime Helpers (Memory-Hard Fast Path)

**Filed:** 2026-05-02
**Track:** Crypto / KDF native fast path
**Sibling FRs:** `pbkdf2_native_runtime_helpers_2026-05-01.md`, `scrypt_native_runtime_helpers_2026-05-02.md`

## Problem

The pure-Simple Argon2id implementation at `src/os/crypto/argon2.spl` follows
RFC 9106 byte-for-byte (BLAKE2b H_0 + H' + permutation P + G compression +
hybrid Argon2id mode), but it is fundamentally memory-hard: each pass writes
`m` KiB and each block update calls G which performs 8+8 invocations of the
BLAKE2b round function on 1024-byte blocks.

Under the Simple interpreter (`bin/simple <spec.spl>`), even minimal valid
parameters (`m=8`, `t=1`, `p=1`, T=32) take a couple of seconds, and the
RFC 9106 §5.3 reference vector (`m=32`, `t=3`, `p=4`, T=32) blows past the
60 s test-runner watchdog. The `argon2id_rfc9106_kat_spec.spl` spec
therefore parks the §5.3 byte-exact KAT behind `pending(...)` until a
native fast path (or a substantially faster compiled-mode interpreter)
lands.

## Acceptance Criteria

- A native runtime helper (or compiled-mode acceleration) for the Argon2
  inner loop — specifically `_g_compress` and the segment-fill iteration
  — that reduces a single G to O(microseconds) rather than O(seconds).
- `argon2id_rfc9106_kat_spec.spl` upgrades its `pending` block to a full
  byte-exact `expect(_bytes_to_hex(tag)).to_equal(...)` assertion against
  RFC 9106 §5.3:
  - password = 32 × 0x01
  - salt     = 16 × 0x02
  - secret   = 8 × 0x03
  - ad       = 12 × 0x04
  - t=3, m=32, p=4, T=32, v=0x13
  - expected tag = `0d640df58d78766c08c037a34a8b53c9d01ef0452d75b65eb52520e96b01e659`
  (RFC 9106 §5.3 verbatim — re-verify when wiring up).
- No new untrusted FFI: the helper either lives in the existing native runtime
  shim or is provided by compiled-mode acceleration.

## Cross-Reference

- Pure-Simple impl: `src/os/crypto/argon2.spl`
- Spec: `test/unit/lib/crypto/argon2id_rfc9106_kat_spec.spl`
- Sibling pattern: `src/os/crypto/scrypt.spl` + `scrypt_native_runtime_helpers_2026-05-02.md`
