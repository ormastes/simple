# Untyped-return guard blind to callback params and non-scalar param idents (2026-08-22)

## Symptom
Bootstrap run13 stage1 HIR phase emitted `untyped function returns a value` **x7**,
all in `src/lib/nogc_async_mut/array.spl`: `array_position`, `array_find`,
`array_find_or`, `array_take_while`, `array_drop_while`, `array_sort_by`,
`array_intersperse`.

`scripts/check/check-untyped-return-value.shs` — the guard added by `f9a7b5cb296`
for exactly this class, whose scope makes `src/lib/*/array.spl` a HARD zero-bar —
reported `PASS — 15190 file(s) scanned, 0 hard-scope offenders` on the same tree.
So this is category (b): a **guard coverage hole**, not new sites and not a
different root cause.

## Root cause — two independent holes in the textual mirror
**Hole A (6 of 7 sites).** `classify_sig` decided "already has a declared return
type" with `untyped = (sig !~ /\) *->/)`. A function-**typed parameter** such as
`predicate: fn(Any) -> bool` contains `) ->`, so *every* callback-taking untyped
function in the tree was classified as typed and never scanned.
Fix: `after_params()` walks to the **balanced** close paren of the parameter list
and tests only what follows it.

**Hole B (`array_intersperse`).** `resolved()` accepted any `return <ident>` whose
name matched a typed parameter. The compiler
(`module_callable_types.spl:infer_simple_type_name_ast`) resolves a param ident
through `hir_type_simple_name`, which yields a name for **scalars only**
(`i64/i32/u64/u32/f64/f32/bool/text`) and `nil` for `[Any]`, a struct, an optional
or a generic ⇒ ambiguous ⇒ fatal. `return arr` with `arr: [Any]` was a real error
the mirror called resolved. Fix: the param-ident branch now requires a scalar
declared type.

**Third rule, added to keep the widened mirror faithful.** Closing A+B initially
produced a false positive (`src/lib/common/option_ce.spl:option_ce_filter`).
`declared_callable_type` bails to `nil` — registering the symbol untyped, with **no
diagnostic** — as soon as any parameter has no declared type (`raw_param.has_type_`
check), so `infer_untyped_return_type` never runs for such a function.
`params_all_typed()` (depth-aware comma split, so `fn(Any, Any) -> i64` is one
param) mirrors that bail. It removed **268 false positives** from the ratchet
baseline (410 → 142, deletions only — no offender was hidden).

## Fix
- `src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/array.spl` — 7 functions each
  (21 signatures) given their true return types: `array_position -> i64`,
  `array_find -> Any?`, `array_find_or -> Any`,
  `array_take_while / array_drop_while / array_sort_by / array_intersperse -> [Any]`.
  The three files are byte-identical for these functions; only `nogc_async_mut` was
  in run13's stage1 set, the other two were the same latent defect.
- `scripts/check/check-untyped-return-value.shs` — holes A/B closed, untyped-param
  bail mirrored, selftest 4 → 7 fixtures (callback-param must FAIL, non-scalar
  param ident must FAIL, untyped-param must PASS).
- `scripts/check/untyped_return_value_baseline.txt` — regenerated (410 → 142).

## Evidence
- Pre-fix detection, new guard on the pre-fix `array.spl` alone:
  `FAIL — 7 hard-scope offender(s)`, naming exactly the 7 log sites with their
  return lines. The old guard PASSed the whole tree with those 7 live.
- Post-fix full run: `PASS — 15190 file(s) scanned, 0 hard-scope offenders, 0 new,
  0 stale (ratchet baseline 142)`.
- Reproduce spec (compiler truth, not text): `test/01_unit/compiler/hir/
  untyped_return_callback_param_shapes_spec.spl` — 5/5 pass; each pre-fix shape
  asserts exactly 1 diagnostic and each fixed shape 0.
