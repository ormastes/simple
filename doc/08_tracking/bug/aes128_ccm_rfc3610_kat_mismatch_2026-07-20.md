# AES-128-CCM RFC 3610 §8 KAT mismatches (ciphertext + auth tag wrong)

- **Date:** 2026-07-20
- **Area:** AES-128-CCM implementation exercised via
  `test/unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl`
- **Severity:** high (real cryptographic KAT mismatches across multiple
  independent RFC 3610 vectors).
- **Status:** CLOSED (2026-11-25) — not an AES-CCM defect; not reproducible on
  any current build. See "Resolution (2026-11-25)" below. **Do not touch the
  expected vectors** — RFC 3610 §8 values are canonical.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl --no-session-daemon
```

```
✗ Vector #1 encrypt: 8-byte AAD, 23-byte PT, M=8 — CT and tag match RFC
    expected [125, 51, 12, 138, 5, 121, 253, 18] to equal
             [23, 232, 209, 44, 237, 233, 38, 224]
✗ Vector #1 decrypt: correct tag returns original plaintext
✓ Vector #1 decrypt: corrupted ciphertext is rejected
✓ Vector #1 decrypt: modified AAD is rejected
✗ Vector #4 encrypt: 12-byte AAD, 19-byte PT, M=8 — CT and tag match RFC
    expected [252, 177, 124, 242, 69, 71, 86, 125] to equal
             [150, 200, 97, 185, 201, 230, 30, 225]
✗ Vector #4 decrypt: correct tag returns original plaintext
    expected authentication tag mismatch to equal
✗ Vector #7 encrypt: M=10 (different tag length) — CT and tag match RFC
    expected [248, 177, 191, 30, 176, 167, 187, 57, 26, 63] to equal
             [4, 140, 86, 96, 44, 151, 172, 187, 116, 144]
✗ Vector #7 decrypt: correct 10-byte tag returns original plaintext
```

9 examples, 6 failures. Notably the "corrupted ciphertext is rejected" /
"modified AAD is rejected" negative-path checks still pass for Vector #1 —
the tag mechanism responds to tampering, it just doesn't match the RFC's
canonical tag/ciphertext for correct input.

## Root-cause hypothesis

Every affected vector's **encrypt** produces a wrong tag (the 8/10-byte
values shown), and the corresponding **decrypt** then correctly reports
"authentication tag mismatch" against the RFC's real tag (since the
implementation's own encrypt doesn't match RFC 3610 either, decrypting the
RFC's canonical ciphertext+tag against this implementation's own AES-CCM
core fails self-consistently). This points at the CCM core itself (CBC-MAC
construction and/or counter-mode formatting per RFC 3610 §2.2/§2.3) producing
wrong tags across multiple AAD/PT/tag-length combinations — not an isolated
single-vector edge case. Not further localized within the CCM
implementation in this triage pass.

## What NOT to do

Do not touch any of the three expected byte arrays — they are RFC 3610 §8
canonical values.

## Affected specs

- `test/unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl` (6 of 9 examples)

## Host-environment classification (2026-09-18)

Audited by the fix-pipeline classification review: **seed-owned** — [env-blocked:deployed-binary]. This row is not executable on the macOS aarch64 host fix lane; it resumes when the blocking condition clears.

## Resolution (2026-11-25) — CLOSED, not an AES-CCM defect

**Root cause of the 2026-07-20 failure transcript:** not the CCM construction.
The failing run was on the x86_64 Rust-seed build of 2026-07-20, whose
text/hex decode path mis-rendered bytes — the transcript's *expected* side
shows `17E8D12C**ED E9**26E0` where the spec source and RFC 3610 §8 both say
`17E8D12C**FD F9**26E0` (`0xFD`→`0xED`, `0xF9`→`0xE9`), the same family as
`char_to_text_yields_placeholder_not_character_2026-09-06`. The RFC 3610 §2.2
/ §2.3 / §3 structures in `src/os/crypto/aes128_ccm.spl` (B0 flags
`Adata|M'|L'`, BE length fields, zero-padding in CBC-MAC, CTR starting at
A_1 with S_0 tag masking, U = T XOR S_0[0..M]) were re-reviewed line by line
against the RFC and are correct.

**History:** this bug was already closed as not-reproducible on 2026-09-12
(commit `62f84df7ea8`, aarch64 seed, 12/12 pass). The later whole-tree
transplant `88aac2ffe28` ("rebase(main): transplant current main tree onto
release/1.0") resurrected an older revision of this document, which is why
the Status above still read OPEN.

**Re-verification 2026-11-25 (x86_64, worktree wt-p1-aesccm, branch
work/p1-aesccm-20261125 = release/1.0.0):**

```
SIMPLE_LIB=src timeout 900 bin/simple.exe test \
  test/01_unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl --mode=interpreter
SPEC FILE VERDICT: ... outcome=OK declared>=12 executed=12 passed=12 failed=0
Results: 12 total, 12 passed, 0 failed
```

The tracked self-hosted `bin/simple.exe` (current grammar), interpreter mode.
Sibling lanes green in the same session:
`test/01_unit/lib/crypto/aes_block_fips197_kat_spec.spl` (AES block primitive,
FIPS 197) and `test/01_unit/lib/crypto/aes256_ccm_kat_spec.spl` (AES-256-CCM)
both PASS.

The expected vectors were independently re-confirmed canonical against
RFC 3610 §8 with pycryptodome 4.6.0 (vector #1: CT
`588C979A61C663D2F066D0C2C0F989806D5F6B61DAC384`, tag `17E8D12CFDF926E0`;
intermediates B0 `5900000003020100A0A1A2A3A4A50017`,
T `2DC697E411CA83A8`, S0 `3A2E46C8EC33A548...`), matching the spec's
constants byte-for-byte — the pass is a real match, not a loosened assertion.

**No code change.** Status: CLOSED (not reproducible on any current build;
original transcript was a stale-seed decode artifact).
