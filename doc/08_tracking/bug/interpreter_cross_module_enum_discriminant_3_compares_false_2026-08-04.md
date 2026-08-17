# Interpreter: cross-module enum variant with discriminant 3 compares FALSE

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-08-04

## Symptom

Under the tree-walk interpreter, reading a payload-less enum value out of a
struct field and comparing it with `==` against the matching enum literal
returns **false** — but only for the variant at **discriminant 3**, and only
when the enum is declared in a *different module* from the comparison site.
The JIT gets the same expression right.

Reproducer using the real `std.ndarray` `DType` enum
(`src/lib/nogc_async_mut/ndarray/mod.spl:30`, variants `F32, F64, I64, Bool`
→ discriminants `0, 1, 2, 3`):

```simple
use std.ndarray.*

fn main():
    val f32a  = array_f32([Float32.new(1.0)])
    val f64a  = array([Float64.new(1.0)])
    val i64a  = array_i64([Int64.new(1)])
    val boola = array_bool([Bool.new(true)])
    print "F32(disc 0) == F32 : {f32a.dtype == DType.F32}"
    print "F64(disc 1) == F64 : {f64a.dtype == DType.F64}"
    print "I64(disc 2) == I64 : {i64a.dtype == DType.I64}"
    print "Bool(disc 3)== Bool: {boola.dtype == DType.Bool}"
```

| discriminant | `SIMPLE_EXECUTION_MODE=interpreter` | JIT (`bin/simple run`) |
|---|---|---|
| 0 `F32` | true | true |
| 1 `F64` | true | true |
| 2 `I64` | true | true |
| **3 `Bool`** | **false — WRONG** | true |

Expected: `true` in every row on both engines.

## Root cause

Discriminant `3` is the runtime's **nil sentinel**. When the interpreter reads a
payload-less enum value out of a struct field that crossed a module boundary,
the discriminant-3 value is indistinguishable from `nil`, so the equality test
against the enum literal fails. This is the same sentinel-3 collision already
recorded elsewhere in this repo for `??` on raw `i64`, for `Option<i64>` value-3
vs `None`, and for defaulted int args.

Axes established by bisection (each probe run on both engines):

- **Discriminant is the axis, not the type**: 0/1/2 pass, 3 fails (table above).
- **Engine is an axis**: JIT correct, interpreter wrong.
- **Module boundary is required**: an enum with the identical shape
  (`F32,F64,I64,Bool`) declared in the *same* file as the comparison compares
  correctly under the interpreter — both when the struct is built directly
  (`Holder(dtype: DT.Bool)`) and when the variant is threaded through a function
  parameter (`fn make(d: DT) -> Holder`). So neither the field read nor
  parameter passing alone is sufficient; the enum must come from an imported
  module.

This matches the known dual-keyed enum-registry behaviour where the discriminant
acts as a cross-module ABI — the importing side and the defining side do not
agree on the encoding for the sentinel-valued variant.

## Impact

Root cause of **7 failures in `test/03_system/feature/scilib`**, all of which
bottom out in a `dtype == DType.Bool` / `dtype != DType.Bool` guard:

- `ndarray_ufunc_spec.spl` — 3 failures. `where_bool()` bails at
  `src/lib/nogc_async_mut/ndarray/ndarray_generators.spl:246`
  (`if mask_values.dtype != DType.Bool: return Err(NdarrayError.UnsupportedDType)`),
  surfacing as `called unwrap on Err: NdarrayError::UnsupportedDType`.
- `ndarray_index_spec.spl` — 2 failures. `ndarray_try_mask()` bails at
  `src/lib/nogc_async_mut/ndarray/ndarray_impl_ops.spl:148` for the same reason;
  `mask()` then **silently swallows the error** via
  `ndarray_or(self.try_mask(...), self)` (`ndarray/mod.spl:498`) and returns the
  array **unfiltered**, so `a.mask(m)` yields `[1,2,3,4]` instead of `[1,3]`.
- `df_missing_values_spec.spl` — 2 failures. `dropna` Any/All go through the same
  `self.values.try_mask(mask)` (`src/lib/nogc_async_mut/df/mod.spl:108`).

The library code itself is **correct** — the same probe returns the right answer
on the JIT (`try_mask is_err: false`, `mask len: 2`). Do not "fix" the ndarray
library; the defect is in the interpreter's cross-module enum encoding.

Repo-wide exposure is wider than scilib: any enum whose **4th** payload-less
variant is compared after being obtained from an imported module is affected.

## Why not fixed now

The fix is in the **Rust bootstrap seed** interpreter's enum encoding /
registry, not in `.spl` product source. Repo rules direct fixes to pure-Simple
source and discourage a seed rebuild unless essential
(`feedback_fix_spl_not_rust`, `feedback_no_bootstrap_unless_essential`), and
renumbering or re-encoding discriminants is explicitly a cross-module ABI change
that needs its own lane — the repo already records that "the enum registry is
dual-keyed and the discriminant is a cross-crate ABI", so a partial change
risks silently mismatching the two keying paths.

A masking workaround in the ndarray library (e.g. reordering `DType` so `Bool`
is not 4th) is deliberately NOT applied: it would hide the defect for one enum
while leaving every other 4-variant enum in the repo broken.

## Re-verification (2026-08-09)

Re-ran the exact reproducer from this doc under
`SIMPLE_EXECUTION_MODE=interpreter bin/simple run` and got the identical
result:
```
F32(disc 0) == F32 : true
F64(disc 1) == F64 : true
I64(disc 2) == I64 : true
Bool(disc 3)== Bool: false
```
Confirms the defect is unchanged. Root cause remains the Rust bootstrap
seed's cross-module enum-registry/discriminant encoding (sentinel-3
collision family), which per repo rules
(`feedback_fix_spl_not_rust`/`feedback_no_bootstrap_unless_essential`) is out
of scope for a `.spl`-only fix and would require a cross-crate ABI change to
the seed's enum registry — not attempted this pass. Status confirmed
unchanged: **OPEN / ARCHITECTURAL**.

## Re-investigated 2026-08-10 (correcting a prior blanket-claim mislabel)

A prior pass in this session had mass-relabeled this doc's classification
using the incorrect claim "the interpreter is implemented entirely under
`src/compiler_rust/**`, off-limits" — false as a blanket statement, since the
self-hosted tree-walk interpreter lives in pure Simple at
`src/compiler/95.interp/*.spl` (`mir_interpreter.spl`,
`mir_interp_intrinsics.spl`, `mir_interp_ops.spl`) and is fully editable.
Re-checked specifically for THIS bug rather than assuming the blanket claim
applied:

- `readlink -f bin/simple` / `bin/simple --version` confirm the currently
  deployed `bin/simple` **is the Rust bootstrap seed**
  (`bin/release/x86_64-unknown-linux-gnu/simple`), which prints the seed
  warning banner. Every reproduction cited in this doc (including the
  2026-08-09 re-verification) ran `SIMPLE_EXECUTION_MODE=interpreter
  bin/simple run`, which — on the currently deployed binary — invokes the
  **seed's Rust interpreter**, not `src/compiler/95.interp/*.spl`.
- `/usr/bin/grep -rln "unknown extern function"` and similar dispatch-string
  greps against `src/compiler/95.interp/` (see companion doc
  `interpreter_extern_registry_gap_blocks_os_specs_2026-08-04.md`
  re-investigation) confirm the pure-Simple interpreter tree does not yet
  implement the enum/struct field-read + cross-module registry dispatch path
  this bug is about — there is no editable `.spl` implementation of the
  behavior in question to fix; the only implementation that runs today is
  the seed's.
- Re-ran the doc's exact `std.ndarray` `DType` reproducer against the
  currently deployed seed binary: unchanged result, `Bool(disc 3)== Bool:
  false` under the interpreter engine, `true` under JIT — same as the
  2026-08-09 measurement.

Conclusion: this is a legitimate architectural classification, but the
original blanket justification for it was wrong; the correct justification
is binary-provenance-based (current `bin/simple` is the seed, and the
seed's Rust interpreter — not the pure-Simple `src/compiler/95.interp/`
tree — is what actually executes `SIMPLE_EXECUTION_MODE=interpreter` today).
Status unchanged: **OPEN — ARCHITECTURAL (Rust seed interpreter, verified
2026-08-10)**.
