# FR: Native scrypt / Salsa20/8 runtime helpers

- **Date filed:** 2026-05-02
- **Status:** OPEN — interpreter-mode V2/V3 KAT vectors blocked
- **Cross-ref:** `src/os/crypto/scrypt.spl` (pure-Simple reference impl)
- **Cross-ref:** `test/unit/os/crypto/scrypt_rfc7914_kat_spec.spl`
- **Cross-ref:** `.claude/memory/feedback_interpreter_bulk_buffer.md`
  (B2 family — extern-backed crypto helpers)
- **Cross-ref:** `doc/02_requirements/feature/pbkdf2_native_runtime_helpers_2026-05-01.md`
  (sister FR; identical pattern for PBKDF2)

## Summary

scrypt (RFC 7914) memory-hard KDF is implemented in pure Simple at
`src/os/crypto/scrypt.spl` using the existing PBKDF2-HMAC-SHA-256
primitive. Algorithm correctness is verified byte-exact against
RFC 7914 §11 Test Vector 1 (N=16, r=1, p=1, dkLen=64) under the
interpreter. Vectors 2 and 3 (N=1024, N=16384) are deferred behind
this FR because they exceed the 60 s test-runner watchdog in
interpreter mode.

## Why pure-Simple optimisation is not sufficient

scrypt's cost is ~`2 * N * p` Salsa20/8 invocations plus `N * p`
ROMix XOR-against-V passes. For RFC 7914 §11 V2:

```
N=1024, r=8, p=16
Salsa20/8 calls per BlockMix = 2*r = 16
BlockMix calls per ROMix     = 2*N = 2048
ROMix calls per scrypt       = p = 16
Total Salsa20/8              = 16 * 2048 * 16 = 524,288
```

Each Salsa20/8 invocation is 4 double-rounds × 8 quarter-rounds = 32
quarter-rounds, each doing 4 add+rotl32+xor cycles. Even before
counting the ROMix XOR-against-V passes (16 × 1024 × 1024-byte XOR
loops), the salsa core alone dominates — and unlike PBKDF2's HMAC,
it is not a SHA core that can be sped up by caching prefix states.
The hot path is fundamentally the salsa quarter-round.

## Proposed externs

Two complementary externs (analogous to `rt_pbkdf2_hmac_sha256`):

```text
# Lowest level — invoked ~524k times per V2; smallest interpreter
# overhead per call is critical here.
extern fn rt_salsa20_8_block(input: [u8]) -> [u8]
```

This keeps BlockMix / ROMix in pure Simple (where the structure is
useful documentation) but offloads the hot 64-byte transform.
Expected speedup: ~50× on V2 based on PBKDF2 sister-FR results.

A higher-level alternative for production hardening:

```text
extern fn rt_scrypt(password: [u8], salt: [u8],
                   n: i64, r: i64, p: i64, dk_len: i64) -> [u8]
```

This bypasses the pure-Simple ROMix V-table allocation entirely (V2
needs 16 × 1 MiB = 16 MiB, V3 needs 16 MiB single-thread, V4 needs
1 GiB) and lets the runtime use a `Vec<u8>` directly. AC-3 (fallback)
is preserved by keeping the pure-Simple `scrypt(...)` as the primary
entry point; the extern is invoked behind a length-check guard, same
pattern as `rt_pbkdf2_hmac_sha256`.

## Acceptance criteria

- **AC-1:** RFC 7914 §11 V1 already passes byte-exact in interpreter
  mode against `src/os/crypto/scrypt.spl` with no extern. (Met by
  initial landing 2026-05-02.)
- **AC-2:** RFC 7914 §11 V2 passes byte-exact under the 60 s
  test-runner watchdog after the extern lands.
- **AC-3:** RFC 7914 §11 V3 passes byte-exact under the 60 s
  test-runner watchdog after the extern lands.
- **AC-4:** Pure-Simple `scrypt` remains the AC-3 fallback when the
  extern is unavailable (early bootstrap, baremetal targets without
  interpreter dispatch).

V4 (N=1048576) remains permanently out of scope for unit tests.

## Out of scope

- Compile-mode (Cranelift) speed optimisation — separate axis.
- yescrypt / scrypt-jane variants — different algorithms.
