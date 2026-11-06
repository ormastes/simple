# JIT `run`: any program importing a comprehension runs fully interpreted (perf)

- **Date:** 2026-11-06
- **Status:** open
- **Severity:** P2 (perf)
- **Area:** `src/compiler_rust/driver/src/exec_core.rs` `run_file_jit`; HIR lowering of comprehensions

## Defect

The JIT `run` lane used to lower comprehensions to nil, which was wrong. d0996c76b7a added
`FallbackReason::Comprehension`, which makes the program fall back to the interpreter.
`run_file_jit` checks the program after `load_module_with_imports` has merged every imported
file (`exec_core.rs:~1173`). So any program that imports a comprehension, even transitively,
runs fully interpreted.

## Reach

27 files in `src/` contain comprehensions. In `src/lib` only three are hot: the skia modules
`skia/backend/cpu/backend.spl:31`, `skia/entity/image.spl:59` and
`skia/bridge/engine2d_bridge.spl:103,114`.

## Fix direction

Desugar comprehensions to a for-loop with push before HIR lowering (about 60 lines). This
restores JIT for all importers. As a stopgap, rewrite the 4 skia sites as plain fill loops.

## Resolution (2026-11-06)

- **Status:** fixed for list comprehensions. `Expr::ListComprehension` is desugared in HIR
  lowering (`hir/lower/expr/control.rs` `lower_list_comprehension`, dispatched from
  `hir/lower/expr/mod.rs`) into
  `do: var __comp_N = []; for pat in iter: [if cond:] __comp_N.push(expr); __comp_N`.
  The loop pattern lives in the `for` scope (no leak); nested comprehensions get unique
  temporaries from a global counter. The AST node has a single `for` clause, so multiple
  `for` clauses do not exist; nesting is covered through nested comprehension exprs.
- `compilability.rs` no longer emits `FallbackReason::Comprehension` for list comprehensions.
  It is kept for `DictComprehension` only (no desugar; still interpreter-only).
- Evidence: probe with filter, nested, imported-module fn, tuple pattern, string iterable and a
  1M-element comprehension runs under `SIMPLE_JIT_STRICT=1` (previously hard error) with
  output identical to the interpreter. 1M comprehension: 0.97 s / 2.6 GB RSS (interpreter)
  -> 0.05 s / 57 MB (JIT).
- Note: the interpreter evaluates all filter conditions before any element expression; the
  desugar interleaves cond/expr per element (identical for pure code).
