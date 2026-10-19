## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: Resolved 2026-05-27

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# AES-XTS IEEE 1619 KAT mismatch after parser cleanup

Date: 2026-05-27
Status: Resolved 2026-05-27
Severity: High — AES-XTS vectors executed but initially failed 14/15

## Symptom

After removing parser blockers in `src/os/crypto/aes_xts.spl`, the IEEE 1619
KAT spec runs in interpreter mode but still fails most vectors:

```bash
bin/simple test test/01_unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl --mode=interpreter --clean --timeout 160
```

Initial observed result after parser cleanup: 1 passed, 14 failed, runtime about
91 seconds.

## Resolution

Two AES-XTS implementation bugs were fixed:

- AES-128 XTS passed raw key bytes into `aes128_encrypt_block`, but that
  function expects expanded round keys. XTS now expands the AES-128 data and
  tweak keys before AES block encryption.
- AES-256 XTS decrypt used a local duplicate key expansion with drift from the
  canonical AES-256 schedule. XTS now uses `aes256_gcm.aes256_key_expansion`
  for AES-256 decrypt.

Verification:

```bash
bin/simple check src/os/crypto/aes_xts.spl test/01_unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl
bin/simple test test/01_unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl --mode=interpreter --clean --timeout 180
```

The KAT now passes 15/15.

## Reopened and fixed 2026-10-19 — aarch64 NEON AES decrypt

Repro (aarch64 host, seed sha256 760f47bf…, interpreter): every XTS decrypt
vector failed (9/15) while every encrypt passed; `SIMPLE_SIMD_TIER=scalar`
passed 15/15. The 2026-05-27 "15/15" was not measured on the NEON tier.

Root cause: `neon_decrypt_block_with_expanded`
(`src/compiler_rust/runtime/src/value/aes.rs`) ran AESD → AESIMC → XOR(round
key) with the plain encryption key schedule. FIPS 197's inverse cipher needs
AddRoundKey before InvMixColumns (or AESIMC-transformed keys, which the x86
path does). Fix: XOR the round key before `vaesimcq_u8`. The spec's IEEE 1619
vectors were correct. Guarded by the Rust test
`fips197_decrypt_known_answer_for_every_tier` and a 16..80-byte round-trip
sweep in the XTS spec. The interpreter seed must be redeployed to carry it.
