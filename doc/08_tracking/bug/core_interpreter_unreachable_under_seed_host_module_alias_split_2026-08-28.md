# Core interpreter unreachable under the Rust seed host: package free-calls fail (E1002) and the AST arena splits into two instances across module-alias families

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
