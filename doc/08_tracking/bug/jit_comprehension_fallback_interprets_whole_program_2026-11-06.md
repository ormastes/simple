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
