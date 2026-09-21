# AES-256-CTR keystream diverges from NIST SP 800-38A vector partway through (AES-128-CTR is correct)

- **Date:** 2026-07-20
- **Area:** AES-256 key schedule / CTR-mode implementation exercised via
  `test/unit/lib/crypto/aes_ctr_nist_spec.spl`
- **Priority:** P1 at filing; no production cryptographic defect was found.
- **Status:** RESOLVED 2026-09-21. The test fixture, rather than the AES
  implementation, had incorrect expected bytes. The expected vector was
  corrected against [NIST SP 800-38A, F.5.5/F.5.6](https://nvlpubs.nist.gov/nistpubs/legacy/sp/nistspecialpublication800-38a.pdf).

## Original symptom

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

## Original root-cause hypothesis (refuted)

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

## Root cause and evidence

The Linux aarch64 run on 2026-09-21 returned the exact NIST ciphertext:
`601ec313775789a5b7a7f504bbf3d228 f443e3ca4d62b59aca84e990cacaf5c5
2b0930daa23de94ce87017ba2d84988d dfc9c58db67aada613c2dd08457941a6`.
The fixture instead expected `...cabf3622`, followed by two entirely different
blocks. The first 29 matching bytes and later divergence came from the mistaken
fixture, not AES-256 key expansion or counter handling. Production code was
already correct and was not changed.

- Before correction: `SIMPLE_LIB=src SIMPLE_RUST_SEED_WARNING=0 timeout 120
  /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple test
  test/unit/lib/crypto/aes_ctr_nist_spec.spl --no-session-daemon` returned
  `4 examples, 2 failures`; the actual AES-256 bytes matched NIST F.5.5.
- After correction: the same spec returned `4 examples, 0 failures`.
- Runtime SHA-256: `11a4cb54e47f29da3a39eda169c656af856221f1f965792a411a0ac95b05c6b3`.

## Affected specs

- `test/unit/lib/crypto/aes_ctr_nist_spec.spl` (2 of 4 examples, both
  AES-256-CTR only)
