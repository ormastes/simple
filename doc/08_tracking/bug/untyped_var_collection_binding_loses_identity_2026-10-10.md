# Untyped `var`/param collection bindings lose runtime collection identity (2026-10-10)

Phase-2 matrix follow-up to
`doc/08_tracking/bug/phase2_matrix_strict_stage2_error_family_2026-10-09.md`
(#2784 landed the missing text-builtin names; this is the next class down).

## Symptom

`unresolved method call: get` / `has` on collection receivers that are
**untyped `var` bindings or untyped parameters** of array/dict literals:

```spl
var c = []        # or: var c = [7, 8]
c.push(1)
val v = c.get(0)  # MIR: unresolved method call: get
```

```spl
fn merge_counts(keys: [text], tmap, fmap, key: text, ...):
    if not tmap.has(key) ...   # MIR: unresolved method call: has
```

`val c = []`, `var c: [i64] = []`, and call-result initializers
(`var c = make_arr()`) all lower correctly — only **untyped `var`** (and
untyped params) lose the identity. ~63 of the remaining 132 matrix
unresolved-method errors trace to this shape (sha3 51, coverage `has` 12).

## Root cause (bisected, minimal repros in build/matrix-probes/)

`lower_array_lit` / `lower_dict_lit` register `runtime_array_locals` /
`runtime_dict_locals` on the literal's own local, and the `val` binding path
threads those flags onto the binding local (mir_lowering_stmts.spl Let
handler, ~1247). The **`var` path drops them somewhere between the init
local and the bound local**: the bound local ends up with MIR type i64, no
collection flags, so `local_is_runtime_array` / `local_is_runtime_dict` miss
and every collection-method arm (`get`/`at`/`first`/`last`/`has`...) falls
through to the loud Unresolved failure. Notably the `SIMPLE_ANYQ_PROBE`
binding probe at mir_lowering_stmts.spl:1260 never fires for the failing
`var` bindings, so the loss is in an earlier sub-branch of the Let handler
(or a different handler entirely) — NOT yet localized. The let-handler is
heavily fenced (self-host landmine history); touching it blind is unsafe.

## Fix applied (house pattern, source side)

Annotate the binding; the annotation path registers the collection identity
correctly (verified under both the strict stage-2 compiler and the seed):

- `src/lib/common/crypto/sha3.spl`: 8x `var X = []` -> `var X: list = []`
  (plus `var buffer: list = ctx[1]` tuple-element reads, 2 sites).
  51 matrix errors. sha3 KAT spec 7/7 still passes under the seed.
- `src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl`:
  4 module-level `var decision_true = {}` -> `: Dict<text, i64> = {}` and
  `merge_counts` params `tmap`/`fmap` annotated `Dict<text, i64>` (the
  annotations had been removed in 2026-07 over a since-fixed runtime parser
  issue; re-verified working on both compilers). 12 matrix errors.
  Coverage aggregation spec 4/4 still passes under the seed.

## Still open (deeper family, same matrix batch)

- `get`/`contains`/`lower`/`unwrap` at test_runner_execute.spl:65/97,
  test_runner_files.spl:57, qemu_test_runner.spl:7,
  driver_mcdc_report_gate.spl:15, qemu_broker_snapshot.spl:13 — annotated
  house pattern already present at those sites; failures are nested
  field-projection receivers (`scoped.budget_decision.reason.contains`),
  Option-unwrap proof, and class-method (`acquire`) resolution. NOT this bug.
- `dynamic_probe.spl` `get`/`withdraw_after_catalog_unload` — separate
  owner-resolution family.
- Repro probes: build/matrix-probes/p17_emptylist.spl, p18_varval.spl,
  p19_one.spl, p20_nonempty.spl, p21_bind.spl, p22_disc.spl
  (p18/p22 discriminate: val passes, var fails, annotated var passes).
