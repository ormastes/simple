# Core interpreter unreachable under the Rust seed host: package free-calls fail (E1002) and the AST arena splits into two instances across module-alias families
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-28  **Status:** OPEN (hand-off: LOADER/module-resolution owner)
**Found by:** perf_interp lane at release tip `bb87306b64c`, seed `phase1_1787877671`

Two independent defects make `src/compiler/10.frontend/core/interpreter` (the AST
"core interpreter", entry `core_interpret`) unrunnable when hosted by the Rust seed
(`<seed> run <wrapper importing compiler.core.interpreter...>`):

## 1. Package-level free-call resolution fails at call time (E1002)

`mod.spl`/`eval_decls.spl`/`env.spl` call same-package functions without imports
(`jit_init_with_backend`, `val_reset`, `env_init`, `hm_make_global_buckets`,
`func_table_reset`, `val_copy_if_value_struct`, ...). When the package is entered via
`use compiler.core.interpreter.*` from an app entry, each fails at CALL time with
`error[E1002]: function 'X' not found`. Adding explicit
`use compiler.core.interpreter.<file>.{X}` imports resolves each one (this lane added
them — see perf_interp.patch). This is also why
`bin/simple run src/compiler/10.frontend/core/interpreter/test_interp.spl`
(the file's own documented invocation) fails today with `function 'val_reset' not found`.

## 2. AST arena global state is DUPLICATED across alias families

After fixing (1), any program whose evaluation READS an identifier fails:

```
val x = 3
print "t10 {x}"   ->  error: semantic: array index out of bounds: index is 10 but length is 0
```

`print "constant"` alone and `val x = 3` alone work. The parser
(`core_frontend_parse_reset`, writing through `compiler.frontend.core._AstExpr.nodes`)
populates `expr_i_val`/`expr_s_val`, but `eval_ident` (`interpreter/eval.spl:495`,
reading the same globals — directly or via the `expr_owner_int` accessor) sees arrays
of LENGTH 0 at valid eids: the seed host instantiated the `10.frontend/core` modules
TWICE — once under the `compiler.frontend.core.*` alias (parser side) and once under
`compiler.core.*` (interpreter side) — each with its own module globals. Same
mechanism family as the alias rewrites in `driver_source_loading.spl:902`.

## Consequence

Tier (b) measurement (seed-hosted pure-Simple interpreter, zero build cost) is
impossible; only a focused native build of the interpreter closure can execute it.
The shipped `run` path also cannot fall back to `core_interpret` until this is fixed
(see sibling record `pure_simple_run_path_hir_interpreter_has_no_loops_2026-08-28.md`).

## Reproduce

`SIMPLE_TIMEOUT_SECONDS=0 <seed> run src/app/perf_core_drv/main.spl t10.spl` with the
2-line program above (wrapper drives jit_init(999999,0) -> eval_init -> ast_reset ->
core_frontend_parse_reset -> resolve_module_locals -> eval_module).

## Fix direction

Canonicalize module identity before global-state allocation (one instance per FILE,
not per alias path), or rewrite `compiler.core.*` <-> `compiler.frontend.core.*` to a
single canonical id in the seed's module loader.

## 2026-09-19 re-verification — `flat_if_chain_interpreter_spec.spl` (suite-2026-09-18 lane)

Spec run (seed `bin/simple.exe`, `--mode=interpreter`): 7 examples, 7 failures, all
executable examples report `expected 0 to equal ...`. Probe evidence confirms both
defects above still hold at HEAD:

- `core_interpret("5 + 7", "f.spl")` returns `0` (and `val_get_int` of it `0`) under
  `<seed> run` — not `-1`, no E1002 diagnostic emitted; the pipeline silently yields
  `0` for every program, including the file's own documented example
  (`fn square(x): x * x; square(7)` → `0`). Import via the
  `compiler.frontend.core.interpreter.mod` alias family reproduces the failure
  identically in `run` and `test` modes.
- The spec's 7th (structural) example additionally pins accessor/section names that
  are absent from the current tree but are NOT phantom: `flat_if_chain_first_arm_get`,
  `flat_if_arm_then_expr_get`, `flat_if_chain_else_expr_get`,
  `resolve_prescan_expr`, `esc_collect_expr_locals` (14 hits in
  `interpreter/resolve.spl` alone) all existed under `src/compiler/10.frontend/core/`
  at `fcbec1c3b62^` and were wiped by `fcbec1c3b62` "fix(merge): restore src/compiler
  and src/lib to origin for phase 1 bootstrap" (2026-08-30). The spec (last touched
  `15c9e602c93`, divergent lineage, same date) was never re-pinned after that
  restore. At HEAD, `resolve.spl` resolves `STMT_IF` by tag in `resolve_expr` with
  no prescan/escape functions. That example therefore fails independent of the seed
  host (stale spec vs intentionally restored tree); re-pinning the spec or
  re-landing the arena refactor is an owner decision and was left unpatched here.

