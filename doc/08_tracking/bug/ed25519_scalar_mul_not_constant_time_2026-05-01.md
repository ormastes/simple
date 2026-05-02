# Bug: `ed_scalar_mul` is not constant-time (Ed25519 timing leak)

- **Date:** 2026-05-01
- **Status:** Open
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

None for the sign path. Verify path is unaffected (scalars are public).
Callers of `ed25519_sign` on adversary-observable timing channels (e.g.
remote SSH, hosted JWT issuance with measurable response latency) should
treat this as a known leak.
