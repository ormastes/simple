# Flaky STATUS_ACCESS_VIOLATION in `smf_with_interp_fallback_function_runs_through_embedded_snapshot` (Windows)

**Date:** 2026-11-27
**Area:** seed driver tests (`src/compiler_rust/driver/src/exec_core.rs`, `jit_top_level_statement_tests`)
**Status:** OPEN

## Symptom
`cargo test -p simple-driver --lib jit_top_level_statement_tests` on Windows (llvm-mingw gnu toolchain) sometimes
aborts with `STATUS_ACCESS_VIOLATION` inside `smf_with_interp_fallback_function_runs_through_embedded_snapshot`.

## Measurements (Fable review, lane binary with the docstring fix)
| Run | Crashes |
|---|---|
| test alone | 0/30 |
| the two `smf_*` tests together | 0/25 |
| whole module, 1 thread | 1/6 |
| whole module, parallel | 2/6 |
| whole module, 1 thread, docstring tests skipped | 1/25 |

In the crash logs the process dies in that test after `imported_simple_function_links_under_strict_jit` ran in the
same process, which points at in-process state leaked from a JIT run into a later SMF run
(`compile_file` / `load_module` / `run_smf_with_args`). The test never reaches `jit_skipped_top_level_statements`,
so the docstring fix is not the cause. Not yet reproduced on a base checkout (a fresh worktree rebuild is ~30 min).

## Repro
`cargo +<channel>-x86_64-pc-windows-gnu test -p simple-driver --lib jit_top_level_statement_tests -- --test-threads=1`
in a loop (CC=clang with llvm-mingw on PATH, gcc-shim on LIBRARY_PATH as in `scripts/setup/build-seed.shs`).
