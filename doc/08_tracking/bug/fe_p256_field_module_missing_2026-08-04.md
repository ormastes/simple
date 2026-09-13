# `std.common.math.field.fe_p256` does not exist; 2 specs and 43 examples cannot run

## Closed 2026-09-13 — the module exists and both specs now execute

**Status: CLOSED (fixed).** The reported defect was that
`src/lib/common/math/field/fe_p256.spl` "was never written", so both specs
failed to load and **43 examples had never executed once**.

`src/lib/common/math/field/fe_p256.spl` exists today. Both specs run, on the
Rust seed `build/vt4/bootstrap/simple.exe` (sha256 `dc138d50276d…`) via
`SIMPLE_BINARY=<abs> simple test`:

| spec | before (reported) | measured 2026-09-13 |
|---|---|---|
| `fe_p256_skeleton_spec.spl` | `1 total, 0 passed, 1 failed` — `Cannot resolve module: std.common.math.field.fe_p256` | **6 total, 6 passed, 0 failed** |
| `fe_p256_full_spec.spl` | same load failure | **55 total, 48 passed, 7 failed** |

61 examples now execute where 0 did. The `Cannot resolve module` error is gone.
That is the whole of what this entry reported, so it closes.

### The 7 residual failures are a DIFFERENT defect — do not reopen this entry for them

They split into two unrelated causes, neither of which is "the module is
missing":

- **2 canonical-zero bugs** in code that *does* exist —
  `fe_to_bytes(p) reduces to 32 zeros (non-canonical zero)` (`expected 255 to
  equal 0`) and `fe_is_zero(p) == true (canonical zero detection)`
  (`expected false to equal true`). Real arithmetic defects: the field element
  equal to the prime `p` is not being reduced to canonical zero.
- **5 missing functions** — `fe_cond_swap` (2 examples) and `fe_pow`
  (3 examples), both `semantic: function ... not found`. The module was written
  without them.

Neither was investigated here. If they are worth tracking they should be filed
as their own entry against `fe_p256.spl`'s contents, since this entry's premise
— that the file does not exist — is no longer true and would mislead anyone
reading it.

MEASURED. The fixing commit was not bisected.

**Status:** OPEN
**Found:** 2026-08-04
**Severity:** medium — P-256 field arithmetic is the base layer under
`crypto/ecdsa_p256.spl`, and its two spec files have never executed a single
example

## Symptom

```sh
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache test/01_unit/lib/math/field/fe_p256_skeleton_spec.spl
  FAIL  test/01_unit/lib/math/field/fe_p256_skeleton_spec.spl (0 passed, 1 failed)
        Error: error: semantic: Cannot resolve module: std.common.math.field.fe_p256
Results: 1 total, 0 passed, 1 failed
```

Same for `fe_p256_full_spec.spl` (419 lines). Expected: the module resolves and
the examples run. Actual: the file fails to load, so all of its examples are
reported as one failure.

## Root cause

The module was never written. `src/lib/common/math/field/` contained no files
at all before this session; `fe25519.spl` was added here, `fe_p256.spl` was
not. A tree-wide search finds the name only in the two spec files and in
`.claude/worktrees/` copies of them:

```sh
$ find . -name 'fe_p256*' | grep -v worktrees
./test/01_unit/lib/math/field/fe_p256_full_spec.spl
./test/01_unit/lib/math/field/fe_p256_skeleton_spec.spl
```

The API the specs pin (from their `use` lists):

| Spec | Imports |
|---|---|
| `fe_p256_skeleton_spec.spl` | `FeP256, fe_zero, fe_one, fe_from_bytes, fe_to_bytes, fe_eq` |
| `fe_p256_full_spec.spl` | the above plus `fe_add, fe_sub, fe_neg, fe_mul, fe_sq, fe_inv, fe_pow, fe_is_zero, fe_cond_select, fe_cond_swap` |

Byte encoding is 32-byte **big**-endian (`fe_one` encodes to 31 zeros then
`0x01`), unlike `fe25519`, which is little-endian.

Note the trailing comment in `fe_p256_skeleton_spec.spl` asserts as fact that
"every op listed in field_trait.spl has a real implementation in
`src/lib/common/math/field/fe_p256.spl` (0 panic call-sites)". That file does
not exist, so the claim is false and should be deleted with the fix.

## Why not fixed now

Not for lack of a plan — for lack of a *fast enough* one, and shipping the slow
one would be worse than shipping nothing.

The generic routes are both unusable. Reduction through
`bignum.bignat.div_mod` is binary long division, ~512 shift-subtract steps per
multiply; `bignum.fixed.mod_reduce_ct` on the 18-limb product is ~540 masked
steps. An inversion is `a^(p-2)`, roughly 512 multiplies, so either path lands
in the millions of interpreter operations and times the spec out — the same
wall that forced `bignum/fixed.spl`'s reduction kernel to be hand-fused this
session (see `_reduce_raw`).

`fe25519` avoids this because 2^255 ≡ 19 folds with a single small multiplier,
which is what makes the ten-limb radix-2^25.5 layout work. P-256's prime,
p = 2^256 - 2^224 + 2^192 + 2^96 - 1, needs a four-term Solinas fold, and the
fold boundaries (224, 192, 96) are not limb-aligned for any radix that also
keeps partial products inside a signed i64 (29 bits is the practical ceiling:
2^29·2^29·9 ≈ 2^61.2). Getting that right is a self-contained piece of work
with its own correctness risk, and it wants to land against the 419-line
`fe_p256_full_spec.spl` as its acceptance gate rather than be bolted on at the
end of an unrelated session.
