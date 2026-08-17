# AES-256-CTR keystream diverges from NIST SP 800-38A vector partway through (AES-128-CTR is correct)

- **Date:** 2026-07-20
- **Area:** AES-256 key schedule / CTR-mode implementation exercised via
  `test/unit/lib/crypto/aes_ctr_nist_spec.spl`
- **Severity:** high (real cryptographic KAT mismatch, curve/mode-specific).
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  F.5.5/F.5.6 values are canonical.

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

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**NOT-REPRODUCED — AES-256-CTR now matches NIST SP800-38A exactly.** Direct
interpreter probe (`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`, rc=0) over
`std.common.aes.modes.aes_ctr_encrypt`, encrypting the two-block SP800-38A F.5
plaintext `6bc1bee22e409f96e93d7e117393172a || ae2d8a571e03ac9c9eb76fac45af8e51`
with IC `f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff`:

```
aes256ctr_got=601ec313775789a5b7a7f504bbf3d228f443e3ca4d62b59aca84e990cacaf5c5
aes256ctr_exp=601ec313775789a5b7a7f504bbf3d228f443e3ca4d62b59aca84e990cacaf5c5
aes128ctr_got=874d6191b620e3261bef6864990db6ce9806f66b7970fdff8617187bb9fffdff
aes128ctr_exp=874d6191b620e3261bef6864990db6ce9806f66b7970fdff8617187bb9fffdff
```

Both key sizes are byte-exact, and crucially the SECOND block (the one this doc
says diverges) matches for AES-256 as well as AES-128. The key-expansion /
counter-increment defect described here is not present in current source
(`src/lib/common/aes/modes.spl:36` `_ctr_increment`, `:58` `aes_ctr_encrypt`).
Recommend CLOSED.
