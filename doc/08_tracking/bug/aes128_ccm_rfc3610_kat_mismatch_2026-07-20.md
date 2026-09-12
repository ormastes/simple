# AES-128-CCM RFC 3610 §8 KAT mismatches (ciphertext + auth tag wrong)

- **Date:** 2026-07-20
- **Area:** AES-128-CCM implementation exercised via
  `test/unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl`
- **Severity:** high (real cryptographic KAT mismatches across multiple
  independent RFC 3610 vectors).
  values are canonical.

- **Status:** CLOSED (2026-09-12) — not reproducible on seed sha256 `3d120a6f`
  (aarch64). **Do not touch the expected vectors** — RFC 3610 §8 values are
  canonical (they were verified canonical; see the re-check below).

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

## Triage 2026-09-12
Rule B: ran `bin/simple test test/unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl` on the deployed seed and it PASSed, so the recorded defect no longer reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-check 2026-09-12

Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed, sha256
prefix `3d120a6f`), `Simple Language v1.0.0-rc.1`. Note the original repro was
recorded on the **x86_64** seed on 2026-07-20; this re-check is aarch64.

```
SIMPLE_RUST_SEED_WARNING=0 timeout 300 bin/simple test \
  test/01_unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl --no-session-daemon
```

```
✓ Vector #1 encrypt  ✓ Vector #1 decrypt  ✓ Vector #1 corrupted-CT rejected
✓ Vector #1 modified-AAD rejected  ✓ Vector #4 encrypt  ✓ Vector #4 decrypt
✓ Vector #7 encrypt  ✓ Vector #7 decrypt  ✓ Vector #7 corrupted-tag rejected
9 examples, 0 failures
✓ empty PT + empty AAD round-trips at M=8
✓ empty AAD + non-empty PT round-trips at M=16
✓ M=16 detects single-bit ciphertext flip
3 examples, 0 failures
SPEC FILE VERDICT: test/01_unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl \
  outcome=OK declared>=12 executed=12 passed=12 failed=0 skipped=0 dropped=0
```

The spec's expected vectors were independently confirmed canonical against
RFC 3610 §8 (Packet Vector #1 CT `588C979A61C663D2F066D0C2C0F989806D5F6B61DAC384`,
tag `17E8D12CFDF926E0`), so the pass is a real match, not a loosened assertion.

### One thing the old transcript reveals, worth recording

In the 2026-07-20 failure output the *expected* tag rendered as
`[23, 232, 209, 44, 237, 233, 38, 224]` = `17E8D12C**ED E9**26E0`, while the
source constant is `17E8D12C**FD F9**26E0`. Two `0xF` high nibbles rendered as
`0xE`. That is a wrong-value defect in the expected side, i.e. in the spec's
`_hex_digit`/`text[i]` path on that build — the same family as
`char_to_text_yields_placeholder_not_character_2026-09-06`, not an AES-CCM
defect. `_hex_digit` was re-probed on the current seed and decodes `F` -> 15
correctly, consistent with the spec now passing.
