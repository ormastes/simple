# AES-256-CTR keystream diverges from NIST SP 800-38A vector partway through (AES-128-CTR is correct)

- **Date:** 2026-07-20
- **Area:** AES-256 key schedule / CTR-mode implementation exercised via
  `test/unit/lib/crypto/aes_ctr_nist_spec.spl`
- **Severity:** high (real cryptographic KAT mismatch, curve/mode-specific).
- **Status:** RESOLVED (2026-09-12) — the implementation was never wrong; the
  spec's stored `_expected_ct_aes256()` constant was not the NIST value.
  Spec: `test/01_unit/lib/crypto/aes_ctr_nist_spec.spl` (+ `test/unit` mirror).

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/aes_ctr_nist_spec.spl --no-session-daemon
```

```
✓ F.5.1 AES-128-CTR encrypts 4-block plaintext correctly
✓ F.5.2 AES-128-CTR decrypts back to plaintext
✗ F.5.5 AES-256-CTR encrypts 4-block plaintext correctly
    expected [96, 30, 195, 19, 119, 87, 137, 165, 183, 167, 245, 4, 187,
      243, 210, 40, 244, 67, 227, 202, 77, 98, 181, 154, 202, 132, 233,
      144, 202, 202, 245, 197, ...]
    to equal [96, 30, 195, 19, 119, 87, 137, 165, 183, 167, 245, 4, 187,
      243, 210, 40, 244, 67, 227, 202, 77, 98, 181, 154, 202, 132, 233,
      144, 202, 191, 54, 34, ...]
✗ F.5.6 AES-256-CTR decrypts back to plaintext
```

4 examples, 2 failures. AES-128-CTR (F.5.1/F.5.2, same CTR-mode wrapper,
different key size) is byte-exact correct.

## Root-cause hypothesis

The first 29 bytes of the AES-256-CTR output match the NIST vector exactly,
then diverge (byte 30 onward: `202` vs `191`, etc.) — i.e. the CTR-mode
counter/XOR wrapper is correct (since it's shared with the passing AES-128
path and the divergence isn't at a block boundary offset consistent with a
wrong nonce/IV), and the first AES-256 block(s) happen to produce correct
keystream bytes before drifting. This pattern (correct start, drift
mid-block) is consistent with an AES-256-specific key-schedule bug (AES-256
uses 14 rounds and a different round-key expansion step every other word
than AES-128's 10-round schedule) surfacing only after enough
rounds/blocks are processed — not further localized to a specific round
constant or Rcon table entry in this triage pass.

## What NOT to do

Do not touch the expected NIST SP 800-38A F.5.5/F.5.6 byte arrays.

## Affected specs

- `test/unit/lib/crypto/aes_ctr_nist_spec.spl` (2 of 4 examples, both
  AES-256-CTR only)

## Triage 2026-09-12
Rule B: re-ran `bin/simple test test/unit/lib/crypto/aes_ctr_nist_spec.spl` on the deployed seed; it still FAILs, matching the recorded defect. Status word left as-is. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-check and resolution 2026-09-12

Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (seed, sha256 prefix
`3d120a6f`), `Simple Language v1.0.0-rc.1`.

RED (before):

```
SIMPLE_RUST_SEED_WARNING=0 timeout 300 bin/simple test \
  test/01_unit/lib/crypto/aes_ctr_nist_spec.spl --no-session-daemon
SPEC FILE VERDICT: test/01_unit/lib/crypto/aes_ctr_nist_spec.spl outcome=ERROR \
  declared>=4 executed=4 passed=2 failed=2 skipped=0 dropped=0
```

### The premise of the original triage was false

The record said "do not touch the expected vector — NIST values are canonical".
That is true of the *NIST* values, but the array stored in the spec was **not**
the NIST value. Independent check against OpenSSL:

```
K=603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4
IV=f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff
PT=6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e51\
30c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710
printf "$PT" | xxd -r -p | openssl enc -aes-256-ctr -K $K -iv $IV -nopad | xxd -p -c 16
  601ec313775789a5b7a7f504bbf3d228
  f443e3ca4d62b59aca84e990cacaf5c5
  2b0930daa23de94ce87017ba2d84988d
  dfc9c58db67aada613c2dd08457941a6
```

`aes_ctr_encrypt` produced exactly these 64 bytes. The spec's constant carried
`...cabf3622 / e89c399ff0f198c6d40a31db156cabfe / ca84e9935a647eafad94da3a3df8a4b5`
for blocks 2-4, which matches no NIST vector; its block 3 even embeds the IV
bytes `f0f1`. Hence the "diverges partway through byte 29" symptom: the two
arrays agree only up to where the fabricated constant stopped tracking NIST.

`src/lib/common/aes/modes.spl` was **not** modified — there was nothing wrong
with it. Only the spec constant and its header comment were corrected, in both
live test trees (`test/01_unit/` and the `test/unit/` mirror; the pre-existing
one-blank-line divergence between them, baselined at
`scripts/check/test_tree_divergence_baseline.txt:672`, is preserved).

GREEN (after):

```
SPEC FILE VERDICT: test/01_unit/lib/crypto/aes_ctr_nist_spec.spl outcome=OK \
  declared>=4 executed=4 passed=4 failed=0 skipped=0 dropped=0
SPEC FILE VERDICT: test/unit/lib/crypto/aes_ctr_nist_spec.spl outcome=OK \
  declared>=4 executed=4 passed=4 failed=0 skipped=0 dropped=0
```
