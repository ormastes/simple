# Flat --entry-closure lane: class-method resolution was NON-DETERMINISTIC (misdiagnosed as a "comment/line-count landmine")

**Date:** 2026-07-24 (root-caused + fixed 2026-07-25)
**Severity:** High (silent miscompile of the *target* program on ~1/3 of builds)
**Lane:** seed `native-build --entry-closure` (SIMPLE_BOOTSTRAP=1, compiler .spl run by the seed)
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Symptom (as originally observed)

Editing interpreted compiler source (first noticed in
`driver_bootstrap.spl`, then `asm_constraints_helpers.spl`, then
`aggregate_intrinsics.spl`) *appeared* to break the compiled `classrepro`
target: `Reg::label()` returned `"0"` instead of `"r1/1"` and a `match` on an
enum-typed field fell through both arms. Build rc=0 (silent). Reverting or
making the edit "line-count-neutral" *appeared* to fix it.

## The misdiagnosis

The "comment lines break it" / "line-count must stay neutral" theory was
**wrong**. The three "data points" (comment block; 2-line vs 1-line coercion;
`!= nil` rewrite) were **coin flips**. The lane is non-deterministic: the SAME
source, rebuilt with `--clean`, alternates green/broken. Measured 2026-07-25:

```
for i in 1..10: native-build --clean classrepro  ->  GREEN, BROKEN, GREEN, ...
```

~2/3 green, ~1/3 broken, with byte-identical inputs. Every "fix" that looked
like it worked was just the next roll landing green; every edit that "broke
it" caught a broken roll. This wasted a whole campaign of contorting edits to
be comment-free / line-neutral.

## Root cause

The compiler is executed by the **seed** (`sc_w41 run …native_build_worker.spl`).
Under the seed, Simple `Dict.keys()` iterates in **hash order that varies per
process** (unlike the native C `SplDict`, which is deterministic). In
`20.hir/hir_lowering/_Items/module_lowering.spl` the flat-lane function loop did:

```
val bootstrap_function_keys = module.functions.keys()   # <- random order per run
# pre-declare: for each key -> self.symbols.define(fn.name, ...)   # assigns symbol ids
# lower:       for each key -> lower_function + accumulate           # emission order
```

Because `module.functions` is a `Dict<text, Function>`, the define() order —
and therefore every function's **symbol id** — changed each build. Combined
with the seed's documented `Dict<text,SymbolId>.get()` returning a shared /
last-defined SymbolId struct (see the lower-loop comment in that file), a
caller like `val r = build()` then non-deterministically failed to recover the
callee's declared **struct return type**. When it failed, `r.label()` fell to
the const-0 method placeholder and `r.mode` read field index 0 instead of the
real offset.

Confirmed by diffing a green vs a broken IR of the same program: identical
function *set*, different emission *order*, and `main` either calling
`@app.classrepro.main.Reg.label` (green) or emitting `add i64 %l9, 0 ; copy`
+ `rt_raw_i64_to_string(0)` (broken). A probe on `resolved_call_hir_return_type`
showed `build`'s symbol id shifting 8↔9 across runs.

## Fix

Impose a deterministic order before symbol-id assignment: sort the function
keys by name (bytewise, via char ordinals — not the `<` operator, which is a
raw pointer compare on the native lane). Added `hir_sort_function_keys` +
`hir_bootstrap_text_lt` in `20.hir/hir_lowering/_Items/module_lowering.spl` and
wired both `module.functions.keys()` sites through it. Result: 10/10 green
classrepro rebuilds (was ~2/3).

## Lesson / guidance

- **Line-count neutrality was a superstition.** Edit compiler source normally.
- Any pass that iterates a `Dict`'s `.keys()`/`.values()` to assign ids or
  build an ordered artifact on the seed-run lane is non-deterministic — sort
  first. Audit other `.keys()`/`.values()`-driven id/order assignments the same
  way (candidates: enum/struct/class registration, symbol-table capture).
- The deeper seed bugs remain (random `Dict` iteration order; shared
  last-defined `SymbolId` struct from `Dict.get`); the sort makes the flat lane
  robust against both. Fixing the seed's Dict semantics is the real long-term
  cure.
- Regression guard: `src/app/classrepro` oracle — but run it **N times**, not
  once (a single green run never proved anything here).
