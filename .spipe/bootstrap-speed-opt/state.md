# Bootstrap Speed Optimization — Rayon Parallelism Tuning

## Status: CLOSED — 2026-05-20

## Task
Optimize Rayon parallelism in the bootstrap pipeline to reduce per-stage compilation time.

## Type
code-quality / performance

## Status
phase-8-ship

## Goal
Configure Rayon thread pool properly for bootstrap compilation — the pool was never actually initialized during bootstrap builds, leaving workers with default 2 MiB stacks and no explicit thread count control.

## Acceptance Criteria
- [x] AC1: Rayon global pool initialized early in `build()` with 16 MiB stack per worker (matching `compile_file_safe` stack)
- [x] AC2: Thread count configurable via `SIMPLE_BOOTSTRAP_THREADS` env var for CI/resource-constrained builds
- [x] AC3: Pool init uses `std::sync::Once` for safe single-initialization across tests and repeated builds
- [x] AC4: Remove broken late `build_global()` call from `compile_entries_parallel` (silently no-oped after first call)
- [x] AC5: `cargo check -p simple-compiler` and `cargo check -p simple-driver` pass cleanly

## Research Findings
1. Bootstrap's `handle_bootstrap` spawns 3 subprocess stages via `Command::new(compiler)` — each stage runs the Rust driver's `native-build` command
2. `native-build` never passes `--threads`, so `NativeBuildConfig.num_threads` is always `None`
3. With `num_threads == None`, the `build_global()` call in `compile_entries_parallel` was never reached
4. Result: Rayon used default pool (2 MiB stack, no named threads) while `compile_file_safe` spawned fresh 16 MiB threads per file inside each rayon worker — double thread allocation
5. The parallel monomorphize (#808) and parallel codegen (#810) modules are NOT in the bootstrap hot path — `monomorphize_module` and codegen run per-file inside `par_iter`

## Changes
- `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`: Added `init_rayon_pool()` with Once guard, 16 MiB stack, `SIMPLE_BOOTSTRAP_THREADS` support; called from `build()` step 0
- `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs`: Removed broken lazy `build_global` from `compile_entries_parallel`
