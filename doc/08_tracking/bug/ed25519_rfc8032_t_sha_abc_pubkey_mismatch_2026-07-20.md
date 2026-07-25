# Ed25519 RFC 8032 §7.1 `T_SHA_ABC` vector: derived public key and signature-verify wrong

- **Date:** 2026-07-20
- **Area:** `src/os/crypto/ed25519_ops.spl` / `src/os/crypto/ed25519.spl`
- **Severity:** high (pubkey derivation / signature correctness for at least
  one canonical RFC vector).
- **Status:** OPEN.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/ed25519_rfc8032_spec.spl --no-session-daemon
```

```
✗ T_SHA_ABC: derived public key matches RFC 8032 §7.1 vector
    expected [236, 23, 43, 147, 173, 94, 86, 59, 244, 147, 44, 112, 225, 36,
      80, 52, 195, 84, 103, 239, 46, 253, 77, 100, 235, 248, 25, 104, 52,
      103, 226, 191]
    to equal [236, 23, 43, 147, 173, 94, 86, 59, 244, 147, 44, 112, 225, 36,
      80, 52, 195, 94, 70, 126, 242, 239, 212, 214, 78, 191, 129, 150, 131,
      70, 126, 43, 240]
✗ T_SHA_ABC: signature verifies under the correct public key
```

The first 18 bytes of the derived key match the RFC vector; bytes 19-31
diverge, then rejoin coincidentally at byte 0 only. `T3` (a different RFC
vector, earlier in the same file) passes both sign-byte-match and
verify — this is vector-specific, not a total break.

15 examples total, 2 failures (`Passed: 13, Failed: 2` in the file's Test
Summary).

## Root-cause hypothesis

Public-key derivation is `pubkey = ed_point_encode(ed_scalar_mul_basepoint(clamped_scalar))`.
`ed_scalar_mul_basepoint` → `ed_scalar_mul_basepoint_simple`
(`src/os/crypto/ed25519_ops.spl:938`) uses a double-and-add loop keyed off
`_ed_scalar_bit(scalar, bit_idx)`. Since T3 passes and T_SHA_ABC fails, this
is most likely a vector-specific edge case (e.g. a particular bit pattern in
the SHA("abc")-derived scalar hitting a carry/reduction corner, or a
clamping edge case) rather than the code being wholly wrong. No further
root-cause narrowing was done here — out of scope for a test-triage pass.

## Possibly related

`ed_scalar_mul_basepoint_simple` is the same function flagged as
constant-time-regressed (branches on `_ed_scalar_bit`) in
`doc/08_tracking/bug/ed25519_scalar_mul_ct_regression_2026-07-20.md`. A
future fix pass should check both together — fixing the CT regression may or
may not also fix this value mismatch; they are filed separately because the
symptoms are distinct (timing-safety vs. a specific vector's wrong output)
and T3 already proves the function is not wrong for every input.

## What NOT to do

Do NOT adjust the expected RFC 8032 §7.1 vector bytes to match the wrong
output — this is a canonical, independently-verifiable published test
vector.

## Affected specs

- `test/unit/lib/crypto/ed25519_rfc8032_spec.spl` (2 of 15 examples)
