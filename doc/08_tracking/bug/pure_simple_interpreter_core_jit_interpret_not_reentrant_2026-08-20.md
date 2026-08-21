# `core_jit_interpret` is not re-entrant — a second eval in one process silently returns WRONG answers

- **Filed:** 2026-08-20
- **Status:** FIXED 2026-08-21 — root cause was the elif arena, not an interpreter reset. Evidence below.
- **Component:** `src/compiler/10.frontend/core/interpreter/**` (pure-Simple frontend tree-walk interpreter)
- **Entry point:** `core_jit_interpret(source, path, threshold)` — `src/compiler/10.frontend/core/interpreter/mod.spl:249`
- **Binary measured on:** `bin/release/x86_64-unknown-linux-gnu/simple`, 59,860,872 bytes, 2026-08-20 06:26:37 UTC

## Summary

Calling `core_jit_interpret` more than once in a single process is unsound. The
second call inherits interpreter global state from the first. The failure is
**not** limited to a missing or errored result — it can produce a plausible but
**incorrect** answer, which is the dangerous shape: a harness that loops over a
corpus in one process prints a table that looks complete and is partly false.

`_core_run_pipeline` (`mod.spl:148`) does call `eval_init()` (`eval_decls.spl:325`
→ `val_reset` / `env_init` / `func_table_reset` / `struct_table_reset` /
`mono_cache_init` / `eval_reset` / `module_loader_init`) and `ast_reset()`. That
set is evidently **incomplete** — some table survives across the reset and holds
stale indices into the re-populated AST/value arenas. Not reset by `eval_init`:
`enum_table_reset` (`eval_tables.spl:695`) and `phantom_reg_reset`
(`eval_tables.spl:809`), among others; the exact culprit is not yet isolated.

## Evidence (each row is a separate process, same binary, same env)

Corpus: `test/fixtures/repro/compiler/class_identity/cases/`, run through
`scripts/check/class_identity_pure_simple_driver.spl` with `SIMPLE_NO_JIT=1
SIMPLE_MODULE_LIMIT=4000`.

| cases evaluated, in order | result |
|---|---|
| `g` alone | `G struct local binding = VAL`, rc=0 — **correct** |
| `f` alone | `F struct literal init = VAL`, rc=0 — **correct** |
| `d` alone | `D class param->field = COPY(n=141)`, rc=0 |
| `g`, `g` | both `VAL` — repeating the *same* case is harmless |
| `c`, `g` | `C ... = REF` then **`G struct local binding = ALIAS(n=10)`** |
| `a`, `g` | `A ... = REF` then `g` rc=-1, **no output at all** |
| `b`, `g` | `b` rc=-1, then the process **dies**: `error: semantic: array index out of bounds: index is 25 but length is 20` |
| all 11, a..k | `b` rc=-1, `d` rc=148, `f` rc=-1, `g` rc=-1; a,c,e,h,i,j,k answered |

The `c`,`g` row is the important one. Case G's source is:

```
var a = SCellG(n: 10)
var b = a
a.n = 11
val got = b.n
if got == 10: print "... = VAL" else: print "... = ALIAS(n={got})"
```

It printed `ALIAS(n=10)`. So `got` interpolated as `10` while `got == 10`
evaluated **false** — value identity/equality is corrupted by the preceding
eval, most likely via the small-int singleton cache (`value.spl:88-102`,
`val_make_int` at `value.spl:168`) versus something that outlived `val_reset()`.

Note also the whole-corpus run **exits 0** while producing these bad results, so
exit status is worthless as a signal here — read the verdict lines.

## Impact

`scripts/check/check-class-identity-engine-matrix.shs` reported
`pureSIMPLE=7/11` and hard-FAILed, blocking all pushes. Worse than the 4 missing
readings: the 7 that *were* produced came from the same contaminated process and
were therefore unverified.

## Workaround in place (not a fix)

The guard now invokes the driver **once per case**, each in a fresh process, via
a new `CLASS_IDENTITY_CASE` env selector in the driver. Fresh-process answers
are the ones reproduced in the table above. See
`scripts/check/check-class-identity-engine-matrix.shs` and
`scripts/check/class_identity_pure_simple_driver.spl`.

This costs one full module load per case and does nothing for any other caller
that evaluates twice in one process. The interpreter still must be made
re-entrant.

## Root cause (2026-08-21)

Not a missing `eval_init()` reset. The surviving state was the **elif arena**
(`elif_cond` / `elif_body` / `elif_else`, `src/compiler/10.frontend/core/_Ast/decl_nodes.spl`).

`ast_reset()` cleared it with a CROSS-MODULE `elif_cond.clear()` from
`_Ast/module_state.spl`. That clear does not reach the arena `elif_new()`
appends to — the same ownership rule already documented in that file for
`module_decl_slots` ("a cross-module `module_decl_slots = []` from here is
dropped anyway", which is why `ast_module_decl_slots_clear()` exists). So the
second parse appended AFTER the first file's entries while the if-statement
nodes were renumbered from 0: the interpreter read the PREVIOUS file's
condition expression id out of `elif_cond[0]`, then indexed the freshly reset
expr arena with it.

Measured with the arena dumped at eval time (`c` then a minimal if/else):

```
[DBG] phase=eval elif_len=1 conds=[19]        # file 1
[DBG] phase=eval elif_len=2 conds=[19, 3]     # file 2 — entry 0 is still file 1's
[DBG expr_get OOB] idx=19 len=10
error: semantic: array index out of bounds: index is 19 but length is 10
```

That explains both observed shapes at once: an out-of-range stale id crashes,
an in-range stale id silently evaluates the WRONG condition — which is exactly
the `ALIAS(n=10)` verdict (`got` printed 10 while `got == 10` "was false": the
`if` never evaluated case G's condition at all).

## Fix

- `src/compiler/10.frontend/core/_Ast/decl_nodes.spl` — new `elif_arena_clear()`,
  owned by the module that owns the arrays.
- `src/compiler/10.frontend/core/_Ast/module_state.spl` — `ast_reset()` calls it
  instead of the three inert cross-module `.clear()`s.
- `src/compiler/10.frontend/core/interpreter/eval.spl` — same defect class,
  found on the way: `eval_reset()` cleared `enum_reg_names`/`enum_reg_variants`
  but left `enum_hm_buckets`/`enum_hm_nexts` pointing at the emptied arrays; it
  now calls `enum_table_reset()`.

## Evidence after the fix

All 11 corpus cases in ONE process, `SIMPLE_NO_JIT=1`:
A,B,C,D,E = REF; F,G,H,I,J,K = VAL; every `rc=0`. Each case re-run
one-per-process gives byte-identical verdicts — that equality IS the
re-entrancy property, and it is what the new gate asserts. (`d` reads REF, not
the `COPY(n=141)` in the table above; both lanes agree, so the difference is
from other landed work, not from contamination.)

## Regression gate

`sh scripts/check/check-interp-reentrancy.shs` — fail-closed, verdict is the
last stdout line (`PASS — <n> case verdict(s) compared, in-process ==
fresh-process` / `FAIL — ...` / `ERROR — nothing was checked`). It runs the
two-file reproduce
(`test/fixtures/repro/compiler/interp_reentrancy/{first,second}_if_else.spl`,
which FAILS before this fix) and then compares every corpus verdict
in-process vs fresh-process. Driven through a new ordered multi-case mode in
`scripts/check/class_identity_pure_simple_driver.spl`
(`CLASS_IDENTITY_CASES`, `CLASS_IDENTITY_DIR`).

## Known neighbouring defect, still open

The match-arm arena (`arm_pattern`/`arm_guard`/`arm_body`/... in the same file)
is cleared by `ast_reset()` the same cross-module way. A module containing a
`match` fails under `core_jit_interpret` with `array index out of bounds: index
is 0 but length is 0` on the FIRST eval — so it is a single-eval defect, not a
re-entrancy one, and adding `arm_arena_clear()` did NOT fix it. Left untouched
here rather than shipping an unverified change; needs its own record.

## Original next step (superseded)

Bisect the surviving global. Suggested approach: add each unreset table
(`enum_table_reset`, `phantom_reg_reset`, the `resolve.spl` caches
`rl_reset`/`cl_reset`/`esc_reset_all`, `lazy_loader_reset`) to `eval_init()` one
at a time and re-run the `c`,`g` pair — that pair is a cheap, deterministic
reproducer that flips a verdict rather than merely erroring.

## Related

- Force-unwrap gap found in the same investigation and FIXED separately:
  `EXPR_FORCE_UNWRAP` (53, `expr!`) had no arm in the pure-Simple evaluator, so
  case B died with `unsupported expression kind: Unknown(53)`. Fixed at
  `src/compiler/10.frontend/core/interpreter/eval.spl` (dispatch arm) and
  `src/compiler/10.frontend/core/_AstExpr/accessors.spl` (`expr_kind_name` did
  not even name the tag). Case B now answers `B class optional field = REF`.
- `doc/03_plan/ui/perf/f1_class_identity_kind_propagation_plan_2026-08-09.md` (S2)

## Re-verification 2026-08-21 — this fix still stands, but the GATE is now RED for a DIFFERENT reason

Re-ran `sh scripts/check/check-interp-reentrancy.shs` on the deployed seed
`bin/release/x86_64-unknown-linux-gnu/simple` (59,947,080 bytes,
2026-08-21 14:27:35 UTC):

```
FAIL — 13 case verdict(s) compared, offenders: first_if_else second_if_else
       no-verdict:a_class_trait_field.spl ... no-verdict:k_struct_method_returned.spl
```

**Not a regression of the elif-arena fix.** `elif_arena_clear()` is present and
called (`_Ast/decl_nodes.spl:1325`, `_Ast/module_state.spl:602`). The driver
never gets as far as evaluating the requested cases: it prints

```
[lexer_fatal] empty source handed to lexer for path '.../interp_reentrancy/Alice'
[case] Alice rc=0        (twice)
```

The loop variable `name` in
`scripts/check/class_identity_pure_simple_driver.spl:182`
(`for name in ordered.split(","):`) reads back as **`Alice`** — the value of the
module-level global `val name = "Alice"` in
`src/compiler/10.frontend/core/test_lang_basics.spl:78`, which the driver
wildcard-imports at line 123. So a module global is clobbering a function-local
binding after a cross-module call returns. Renaming the loop variable moves the
failure to a different local (`error: semantic: type mismatch: cannot convert
dict to int`), which is the same defect hitting a different name.

Filed separately as
`doc/08_tracking/bug/seed_interpreter_module_global_clobbers_function_local_2026-08-21.md`.
This record stays FIXED; the gate cannot go green until that one is fixed.
