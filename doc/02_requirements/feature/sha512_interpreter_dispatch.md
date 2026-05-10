# Requirements: sha512_interpreter_dispatch

## Summary

Add interpreter-mode dispatch for the SHA-512 family runtime externs so that
`os.crypto.sha512.sha512()` (and its dependencies `rt_sha512_K` /
`rt_sha512_H` / `rt_sha512_hash` / `rt_sha512_byte`) work under
`bin/simple <spec>.spl` (interpreter mode), not only in baremetal/Cranelift
compiled mode.

This is a **blocker** for W14-D (SLH-DSA-192s + SLH-DSA-256s parameter
variants). FIPS 205 §11.2.1 Table 4 specifies the SHA-2 family of
SLH-DSA-{192s,256s} uses **SHA-512** (block size 128, prefix length
128 - n bytes). There is no SHA-256 fallback for these parameter sets.

## Empirical Evidence (2026-05-02)

- Probe: `bin/simple /tmp/sha512_probe.spl` (calling `sha512([0x61,0x62,0x63])`)
  fails with: `error: semantic: unknown extern function: rt_sha512_hash`.
- `grep -rn 'rt_sha512' src/runtime` returns no matches — the SHA-512
  externs declared by `src/os/crypto/sha512.spl` (`rt_sha512_K`,
  `rt_sha512_H`, `rt_sha512_hash`, `rt_sha512_byte`) have no interpreter
  dispatch path in the Rust seed runtime.
- `src/os/crypto/ed25519.spl:17` already documents this: "*baremetal C
  `rt_sha512_*` extern that has no interpreter dispatch.*" — the same
  blocker has previously been worked around by ed25519 callers using
  reduced-coverage interpreter tests.
- `src/os/crypto/sha512.spl:204` defines `rt_sha512_hash` /
  `rt_sha512_byte` as baremetal C-side externs ("WORKAROUND: Uses C-side
  implementation because baremetal array push/len are unreliable").
- Pure-Simple fallback `_sha512_pure_simple` (line 207+) is also gated on
  `rt_sha512_K` / `rt_sha512_H` constant accessor externs that have no
  interpreter dispatch.

## Requirements

- REQ-SHA512ID-001: The interpreter must dispatch `rt_sha512_hash(data, _)`
  to a working SHA-512 implementation that produces the FIPS 180-4 digest
  bytes consumable by `rt_sha512_byte(i)` for i in 0..63.
- REQ-SHA512ID-002: The interpreter must dispatch `rt_sha512_byte(i)`
  returning the i-th byte of the most recent `rt_sha512_hash` invocation.
- REQ-SHA512ID-003: The interpreter must dispatch `rt_sha512_K(i)` and
  `rt_sha512_H(i)` constant accessors returning the FIPS 180-4 SHA-512
  K-table and IV-table u64 values, OR alternatively
  `src/os/crypto/sha512.spl` must be refactored to inline the K/H tables
  in pure Simple so the constant-accessor externs are no longer needed.
- REQ-SHA512ID-004: After dispatch lands, `os.crypto.sha512.sha512(b"abc")`
  in interpreter mode must produce the FIPS 180-4 vector
  `ddaf35a193617aba cc417349ae204131 12e6fa4e89a97ea2 0a9eeee64b55d39a
  2192992a274fc1a8 36ba3c23a3feebbd 454d4423643ce80e 2a9ac94fa54ca49f`.
- REQ-SHA512ID-005: An interpreter-mode SHA-512 NIST FIPS 180-4 KAT spec
  must accompany the dispatch, mirroring the existing
  `test/unit/lib/crypto/sha2_nist_vectors_spec.spl` coverage for SHA-256.

## Downstream Unblocks

Landing this FR unblocks:

1. **W14-D** — SLH-DSA-SHA2-192s and SLH-DSA-SHA2-256s parameter variants
   (FIPS 205 §11 Table 2). Both require SHA-512 for F / H / T_l / PRF /
   PRF_msg / H_msg per Table 4. The 192s/256s `slh_keygen_internal` /
   `slh_sign_internal` / `slh_verify_internal` paths cannot pass any
   interpreter-mode KAT until SHA-512 is dispatchable.
2. **Wave 15** — SLH-DSA-{128f, 192f, 256f} fast variants (same SHA-512
   dependency for the 192f/256f set).
3. **HKDF-SHA-512** / **HMAC-SHA-512** interpreter-mode KAT specs.
4. **Ed25519 interpreter-mode coverage** (currently relies on baremetal
   compiled mode for any test that exercises the SHA-512 hashing path).

## Non-Goals

- Implementing SHA-512 in pure Simple at the call site (`slh_dsa_192s.spl`
  / `slh_dsa_256s.spl`) is **explicitly out of scope** for the W14-D wave
  per the wave's pure-Simple-only constraint and
  `feedback_extern_bootstrap_rebuild.md` (extern additions need a
  bootstrap rebuild). The dispatch belongs in the runtime, not duplicated
  in every caller.

## Verification

- The 128s baseline currently passes 7/7 tests in interpreter mode at
  ~32 s fresh (`test/unit/lib/crypto/slh_dsa_128s_spec.spl`,
  measured 2026-05-02). Any SHA-512 dispatch landing must keep this green
  and additionally green a sibling `slh_dsa_192s_spec.spl` /
  `slh_dsa_256s_spec.spl` once W14-D resumes.

## References

- NIST FIPS 205 — Stateless Hash-Based Digital Signature Standard, August
  2024. https://csrc.nist.gov/pubs/fips/205/final
- NIST FIPS 180-4 — Secure Hash Standard.
- `src/os/crypto/sha512.spl` — pure-Simple + extern declarations.
- `src/os/crypto/ed25519.spl` — pre-existing victim of the same gap.
- `.claude/memory/feedback_extern_bootstrap_rebuild.md` — rule that
  forced this FR rather than an in-line workaround.
- `.claude/memory/feedback_compile_mode_false_greens.md` — rule that
  forced empirical interpreter-mode verification of any new KAT.
