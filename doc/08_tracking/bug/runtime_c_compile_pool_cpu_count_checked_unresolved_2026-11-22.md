# `runtime_c_compile_pool_v1.spl` imports `cpu_count_checked` from a module that does not export it

- Found: 2026-11-22, Windows MSVC release bootstrap, Phase 4 lane (full CLI built by
  the admitted Phase 2 compiler, `admit-built-stage2-compiler-tests.shs`).
- Symptom: `HIR lowering error in src/compiler/70.backend/backend/runtime_c_compile_pool_v1.spl:
  unresolved name: cpu_count_checked at ...:71:26`; `compiler_cli_build` FAIL.
- Cause: `use std.io_runtime.{process_spawn_async, cpu_count_checked}` (introduced by
  `e0aea49c8e9`). `src/lib/io_runtime.spl` does not export `cpu_count_checked`; it is
  `pub fn cpu_count_checked` in `src/lib/nogc_sync_mut/io/sysinfo_ops.spl`, which every
  other caller imports.
- Fix: import it from `std.nogc_sync_mut.io.sysinfo_ops`.
- Retest: full-CLI build (`compiler_cli_build` row) with the next compiler generation.
