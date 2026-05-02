# Bug: `ed_scalar_mul` is not constant-time (Ed25519 timing leak)

**Status: FIXED 2026-05-01 — replaced naive double-and-add with always-add-and-select on the secret-scalar path.**

Resolution: Added `ed_point_cselect(p0, p1, choose_p1: u64)` in
`src/os/crypto/ed25519.spl` using the same XOR-mask discipline as
`fe_cswap` in `curve25519.spl` (`mask = 0 - choose_p1`,
`out = a ^ (mask & (a ^ b))`). Rewrote the inner loop of `ed_scalar_mul`
to ALWAYS execute `ed_point_add` and `ed_point_double` on every one of the
256 scalar bits, with the conditional add replaced by a constant-time point
select keyed on the bit value. No data-dependent branch on scalar bits, no
early exit, no `if`-on-scalar inside the function body. Compiler cannot
branch-fold the XOR/AND arithmetic (per the B6 memory note on CT compares;
verified empirically — `fe_cswap` uses the identical pattern in the
Curve25519 Montgomery ladder and works under the seed compiler today).

Verification:
- All 15 examples in `test/unit/lib/crypto/ed25519_rfc8032_spec.spl` still
  PASS byte-exact in interpreter mode (~8.1s, ~2× the previous leaky form,
  matching the bug doc's prediction for option 1).
- New spec `test/unit/lib/crypto/ed25519_ct_property_spec.spl` (5/5 PASS,
  ~4.8s) covers determinism, sign+verify under low-Hamming-weight (seed
  `0x00 * 32`) and high-Hamming-weight (seed `0xFF * 32`) seeds, and a
  structural CT inspection that reads the live source of
  `src/os/crypto/ed25519.spl`, locates the body of `fn ed_scalar_mul`, and
  asserts none of the leaky-form fingerprints (`if ((byte_val`,
  `if scalar[`, `) & 1) == 1`) survive AND that the body MUST contain
  `ed_point_cselect`.

Approach picked (option 1, always-add-and-select) over option 2 (Montgomery
ladder): one CT path covers all four call sites — including the variable-
base `ed_scalar_mul(k, big_a)` in `ed25519_verify` — without forcing two
parallel implementations or a different point representation. Verify is on
public data so doesn't strictly need CT, but a uniform CT path is fewer
moving parts.

- **Date:** 2026-05-01
- **Status:** FIXED 2026-05-01
- **Module:** `src/os/crypto/ed25519.spl`
- **Severity:** Side-channel (timing)
- **Surfaced by:** Pure-Simple rewire of the Ed25519 public API
  (`ed25519_rfc8032_vector_mismatch_2026-05-01.md`).

## Symptom

`fn ed_scalar_mul(scalar: [u8], p: EdPoint) -> EdPoint` at `src/os/crypto/ed25519.spl`
uses a conditional add:

```spl
if ((byte_val.to_u64() >> bit) & 1) == 1:
    result = ed_point_add(p1: result, p2: q)
q = ed_point_double(q)
```

The conditional `ed_point_add` only executes on bits whose value is `1`, so the
loop's wall-time is correlated with the Hamming weight of the scalar. On the
sign hot path, the scalar argument is the **clamped secret scalar `a`** derived
from the seed — every bit of which is meant to be confidential. This is a
classic constant-time-discipline violation.

`feedback_no_coverups.md` and AC-3 of the Ed25519 RFC-vector task explicitly
require constant-time discipline. Calling it out instead of silently shipping.

## Pre-existing vs. introduced

The function existed prior to the RFC-vector fix, but was not reachable from
the public sign path (which delegated to a C extern). Rewiring to pure-Simple
made it reachable. The leak is therefore *exposed*, not *introduced*, but the
fix surface is the same: replace the conditional add with a constant-time form.

## Suggested fix path

Adopt either:

1. **Always-add-and-select** — execute `ed_point_add` on every bit, but use a
   constant-time `select(bit, P, Q)` to choose between `result` and
   `result + q`. ~2× wall-time vs. current branchful form, but constant
   regardless of scalar.
2. **Montgomery ladder** — fewer operations than (1) and naturally
   constant-time, but requires a different point representation than the
   current extended-coordinate code. More work.

Either form must also use a constant-time `fe_select` / `fe_cswap` to avoid
leaking via field-element comparisons in `ed_point_add`.

## Acceptance test

A timing test cannot be reliably written in this interpreter; correctness can
be checked by re-running `test/unit/lib/crypto/ed25519_rfc8032_spec.spl`
(must still pass byte-exact) plus a property test that randomly-chosen
secrets all derive the same public keys.

## Workaround until fixed

(No longer applicable — the fix landed 2026-05-01. Historical text below.)

None for the sign path. Verify path is unaffected (scalars are public).
Callers of `ed25519_sign` on adversary-observable timing channels (e.g.
remote SSH, hosted JWT issuance with measurable response latency) should
treat this as a known leak.
