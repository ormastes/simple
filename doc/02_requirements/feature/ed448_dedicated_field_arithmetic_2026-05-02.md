# Feature Request — Dedicated 16-Limb Field Arithmetic for Ed448

**Filed:** 2026-05-02 (W14-F)
**Module:** `src/os/crypto/ed448.spl`
**Driver:** RFC 8032 §7.4 KAT cannot complete in interpreter mode
**Discipline:** `feedback_no_coverups.md` — perf gap surfaced, not swallowed

## Symptom

`bin/simple test test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl` exceeds the
60-second per-it watchdog on the **first** assertion (T1: derived public key
matches RFC 8032 §7.4 Blank vector). That assertion does a single
`ed448_keygen(SEED_T1)` call, which is one ~447-bit scalar multiplication of
the base point B. It does not complete.

## Root cause

`ed448.spl` uses the proven-correct generic-bigint backend (`_bi_*`, 30-bit
limbs, file-private copies of the same helpers established by
`os/crypto/curve25519_bigint.spl` and `os/crypto/rsa_fallback.spl`).

Each scalar multiplication is roughly:
- 447 doublings + ~223 adds (variable-time double-and-add)
- Each Edwards448 group op = ~10 field multiplications
- Each field multiplication = `_bi_mul` of ~15-limb operands (≈225 limb-mul
  ops) followed by `_bi_mod` against the 448-bit prime `p` (bit-by-bit
  binary reduction over 448 bits)

That's on the order of 10^7 interpreter-evaluated arithmetic ops per
scalar-mul. Curve25519's bigint backend has the same shape but runs on a
255-bit modulus (~9 limbs) and 254 ladder steps — Ed448 is roughly 4-5x
slower per scalar-mul, well past the 60s watchdog.

## Why this isn't fixed in the W14-F change

The dedicated path mirrors what `Fe25519` (in `os/crypto/curve25519.spl`) is
to Curve25519: a hand-rolled 9-limb 25/26-bit field type with Solinas-style
modular reduction that exploits the special form `p = 2^255 - 19`. For Ed448,
the equivalent is 16-limb 28-bit limbs (or 8 × 56-bit) with reduction
exploiting `p = 2^448 - 2^224 - 1` (Solinas, "Goldilocks" prime).

That's 600-1000 net new lines of carefully-validated limb arithmetic — out of
W14-F's 2-3-attempt scope. Per advisor reconcile, the trade was:
- Bigint backend = correctness-confidence high, perf-confidence low
- Dedicated 16-limb backend = perf-confidence high, correctness-risk high
  (vector-mismatch debug spirals on add/double/reduction in 2-3 attempts)

W14-F shipped the bigint backend.

## Proposed fix

Add `Fe448` (parallel to `Fe25519`) to `os/crypto/curve25519.spl` companion or
`os/crypto/ed448_field.spl`:

- 16 × 28-bit limb representation (or 8 × 56-bit for register-pair targets)
- `fe448_add / fe448_sub / fe448_mul / fe448_sq / fe448_invert / fe448_neg`
- Solinas reduction for `p = 2^448 - 2^224 - 1`:
  the reduction collapses high limbs back into the low half via the identity
  `2^448 ≡ 2^224 + 1 (mod p)`, exploiting the 224-bit overlap
- `fe448_from_bytes / fe448_to_bytes` (57-byte LE)

Then rewire `ed448.spl` to use `Fe448` in place of the file-private `_bi_*`,
and rerun `test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl`. Expected runtime
based on Fe25519's interpreter perf scaled to 448-bit: 10-30 seconds per
sign/verify, fitting under the 60s watchdog with two vectors.

## What landed in W14-F (current state)

- `src/os/crypto/ed448.spl` — full RFC 8032 §5.2 implementation:
  - Bigint backend (`_bi_*`)
  - Ed448 field constants (p, d, L) and base point (verified against curve eq)
  - Untwisted Edwards448 add/double formulas (a=1, derived from §5.2.4 — NOT
    copied from Ed25519's HWCD08 a=-1 formulas)
  - Point encode/decode (57 bytes LE, sign bit in MSB of byte 56)
  - SHAKE256 dom4 prefix `"SigEd448" || phflag || OLEN(ctx) || ctx`
  - Pruning per §5.2.5 (bytes & 0xfc, byte 55 |= 0x80, byte 56 = 0)
  - `ed448_keygen / ed448_sign / ed448_verify` public API
- `test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl` — 8 specs over 2 RFC §7.4
  vectors (Blank empty + 1-byte 0x03), positive + negative verify paths

The module **loads** cleanly (interpreter sanity check passes). The `to_equal`
byte-match assertions (per W11-A spec runner) cannot fire end-to-end until
either (a) the dedicated `Fe448` backend lands, or (b) the bigint backend is
JIT-compiled at a much higher tier than today's interpreter.

## Acceptance criteria

- [ ] `bin/simple test test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl` passes
      all 8 specs in interpreter mode, ≤ 60s per spec
- [ ] No use of `skip()`, no weakened assertions, no swallowed errors
- [ ] No removal of the bigint backend without a parallel pure-Simple
      replacement that passes the same KAT vectors

## Cross-refs

- `feedback_no_coverups.md` — discipline for surfacing perf as a feature
  request rather than masking with skips/timeouts
- `feedback_compile_mode_false_greens.md` — must verify in interpreter mode;
  compiled-mode passes don't prove correctness
- `os/crypto/curve25519.spl` (`Fe25519`) — the pattern to mirror
