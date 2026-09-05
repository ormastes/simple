# P-256 ECDH imports a field-arithmetic module that has never existed

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (independent re-verification pass).
  The module now exists at the exact imported path and defines every imported
  name. Checked `src/lib/common/math/field/fe_p256.spl`: `struct FeP256` :33,
  `fe_zero` :53, `fe_one` :56, `fe_add` :115, `fe_sub` :136, `fe_mul` :239,
  `fe_sq` :296, `fe_inv` :299, `fe_from_bytes` :337, `fe_to_bytes` :357,
  `fe_eq` :91 — all 11 names on the `use std.common.math.field.fe_p256.{...}`
  list at `src/os/crypto/ecdh_p256.spl:46-53` resolve. Landed by
  `306aebd15daa` ("feat(crypto): implement the P-256 field layer that p256.spl
  imported but did not exist"). **Verified by source inspection only** — the
  `p256_ct_property_spec.spl` run in the Symptom section was not re-executed,
  so this closes the *missing-module* defect, not any arithmetic-correctness
  claim about the new field layer.
- Found: 2026-08-17, `test/01_unit/lib/crypto` sweep
- Severity: **HIGH** — P-256 ECDH is non-functional, and it fails at *runtime*,
  not at build time. Security-relevant surface.

## Symptom

```
FAIL test/01_unit/lib/crypto/p256_ct_property_spec.spl (1 passed, 4 failed, 1880ms)
     Error: semantic: function `fe_from_bytes` not found;
            semantic: function `fe_from_bytes` not found;
            semantic: function `fe_from_bytes` not found
```

## Root cause

`src/os/crypto/ecdh_p256.spl:46` imports its entire field-arithmetic vocabulary
from a module that does not exist:

```
use std.common.math.field.fe_p256.{
    FeP256,
    fe_zero, fe_one,
    fe_add, fe_sub,
    fe_mul, fe_sq, fe_inv,
    fe_from_bytes, fe_to_bytes,
    fe_eq
}
```

Verified absent:
- `src/lib/common/math/field/fe_p256.spl` — does not exist;
- `find src -name 'fe_p256*'` — **no hits anywhere**;
- `src/lib/common/math/field/` — **the directory itself does not exist**.

The only `fe_from_bytes` in the tree is
`src/lib/common/crypto/ed25519.spl:454`, which is **Curve25519** field
arithmetic operating on `Fe25519` — a different prime field. It is not a
substitute for P-256 and must not be wired in as one.

Call sites that therefore die at runtime, all in `ecdh_p256.spl`:
`:60`, `:68` (curve constants), `:319`, `:320` (`px`/`py` decode in the public
key path).

## Why this shipped silently

**An unresolved `use` is only a WARNING.** The file compiles, exports its
public API, and every call fails at runtime instead. `p256_keypair_pub` is
reachable and looks implemented.

This is the **fourth independent instance of this exact class found on
2026-08-17**, and the most severe:

| # | site | fixed? |
|---|---|---|
| 1 | `src/lib/nogc_sync_mut/dns/wire.spl` — `use string.{char_from_code}` | fixed `3d56c94653e` |
| 2 | `src/lib/nogc_sync_mut/smtp/utilities.spl` — same | fixed `3d56c94653e` |
| 3 | 5 tier mirrors (`buffer/`, `smtp/` across 3 tiers) — same | fixed `f25f03bdc85` |
| 4 | **this one** — P-256 ECDH field arithmetic | OPEN |

Instances 1-3 were a typo'd module name. This one is different in kind: the
module was **never written**, and a whole curve implementation is missing
underneath a public API that advertises it.

## NOT a stale-binary artifact

Ruled out explicitly. The deployed `bin/simple` (mtime 2026-08-16 22:59) does
lag several fixes landed 2026-08-17, and one other RED in this sweep
(`GreenTask.thunk`) was traced to exactly that. This one is different: the
imported module is **absent from the source tree**, so no binary, however
fresh, could resolve it.

## Scope to fix — do NOT stub, and do NOT substitute Curve25519

Required: a real P-256 (secp256r1, p = 2^256 - 2^224 + 2^192 + 2^96 - 1) field
implementation exporting `FeP256`, `fe_zero`, `fe_one`, `fe_add`, `fe_sub`,
`fe_mul`, `fe_sq`, `fe_inv`, `fe_from_bytes`, `fe_to_bytes`, `fe_eq`.

The spec that caught this is named `p256_ct_property_spec` — **ct = constant
time**. Any implementation must be constant-time with respect to secret data:
no secret-dependent branches, no secret-dependent indexing. A naive
BigInt-backed placeholder would turn this RED into a GREEN that leaks keys by
timing, which is strictly worse than the current honest failure.

Estimate: a correct constant-time P-256 field is a substantial, security-
critical module — comparable to the existing `ed25519.spl` field layer, and it
must be validated against published test vectors (never self-comparison, per
the false-green guard in the SPipe skill).

Spec left RED per `.claude/rules/testing.md`.

## Recommendation beyond this bug

Four instances in one day is not a coincidence. **Make an unresolved `use` a
hard error, or add a lint that fails the build on one.** Every instance here
compiled cleanly, passed every structural push guard, and failed only when a
spec happened to execute the affected line. In this case that silence hid a
missing curve implementation behind a live crypto API.
