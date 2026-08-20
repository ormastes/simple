# `core_jit_interpret` is not re-entrant — a second eval in one process silently returns WRONG answers

- **Filed:** 2026-08-20
- **Status:** OPEN (worked around at the call site; the defect itself is unfixed)
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

## Next step

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
