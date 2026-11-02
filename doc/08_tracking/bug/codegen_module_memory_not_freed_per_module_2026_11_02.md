# Codegen memory not freed per module: ~21 GB per 48-module MIR shard (2026-11-02)

- **ID:** codegen_module_memory_not_freed_per_module_2026_11_02
- **Priority:** P1 (phase-3 shard workers exceed their budget; host OOM risk)
- **Status:** fix landed in source; RSS AFTER pending a stage3 producer
- **Related:** `native_codegen_unscoped_rss_growth_2026_10_24.md`,
  `llvm_bootstrap_string_cache_scope_escape_2026_10_25.md`,
  `stage2_per_module_codegen_scales_with_closure_2026-11-02.md`, lane 3 (#5791, Both/SMF staging)

## Symptom
Phase-3 runs 20-23b (`C:/dev/p3new/r11/run20*`, `run21`-`run23`, frozen
`C:/dev/p3new/stage2.exe`): each MIR shard worker logs
`[NATIVE] codegen: 48 uncached module(s), concurrency=1` and grows to ~21 GB
while compiling its 48 modules sequentially (`[shard] ... worker budget=...`
is far below the observed size). The runs already set
`SIMPLE_CODEGEN_MODULE_SCOPE=1`, and the logs contain zero `[codegen-scope]`
warnings, so the opt-in scope was active and still did not bound growth.

## Cause
1. **The LLVM object-path scope promoted the IR out.** `llvm_compile_module_direct_to_path`
   (`70.backend/backend/llvm_codegen_adapter.spl`) scoped only translation, then
   `transient_promote(llvm_ir)` before `compile_ir_to_object_path`. With no outer
   scope, a promoted value becomes persistent: the whole module IR text (tens to
   hundreds of MB for the 900 KB-object modules) stayed live until the worker
   exited. The object emission after it (`rt_file_read_bytes` of the staged
   object for the magic check, argv, paths) also ran unscoped.
2. **Scope was opt-in.** Without `SIMPLE_CODEGEN_MODULE_SCOPE=1` neither the
   object-path lane nor `compile_module_with_backend_scoped_v1` freed anything.

## Fix
- One scope now covers translation **and** object emission. The function
  returns a scalar status, so nothing is promoted; scope end frees IR text,
  translator scratch and the staged-object byte copy.
- Tool discovery (`find_llc`/`find_clang`, which fill `_find_tool_cache_*` and
  strict tool bindings) is warmed before the scope opens.
- `llvm_codegen_module_scope_enabled_v1()`: on by default; `SIMPLE_CODEGEN_MODULE_SCOPE=0`
  is the explicit opt-out. Used by both the object-path lane and
  `compile_module_with_backend_scoped_v1`.
- Exclusions kept/added: `SIMPLE_BOOTSTRAP=1` (bootstrap string cache and
  `llvm_bootstrap_last_object_path()` globals), `SIMPLE_LLVM_BITCODE_DEBUG=1`
  (lazy llvm-as/opt discovery), any caller-owned scope (refused with warning).
- Not changed: the process-parallel pool gate (`driver_aot_native_output.spl`
  `_driver_codegen_pool_lane_reason_v1`) still treats only an explicit `=1` as
  a reason to stay serial, so default-on does not disable the pool. SMF/`Both`
  paths re-read `ctx.mir_modules`/capsule MIR, which is outside every scope
  (MIR is promoted before codegen), so they are unaffected.

## Not addressed here
- The frozen capsule batch keeps every module's MIR for the shard. That MIR is
  immortal from lowering, so per-module batch release frees nothing until MIR
  lowering itself is session-scoped (lane 3 / BSM).
- MIR backend optimization copies on the backend-session path run outside the
  scope because they append to the persistent SIMD provider report.

## Verification
- Spec: `test/01_unit/compiler/backend/llvm_codegen_module_scope_default_spec.spl`
  (default-enabled policy; per-module heap growth < 4 KiB over 16 emissions).
  Red on base: `llvm_codegen_module_scope_enabled_v1` absent (seed-labeled: the
  Rust seed cannot parse current `src/lib`, frozen stage2 has no `test`).
- RSS before: ~21 GB per 48-module shard worker (runs 20-23b).
- RSS after: pending a stage3 producer built from this source (no stage2
  whole-program builds allowed on the shared host). A `[codegen-scope] WARNING`
  line in the next run means the scope was refused and the saving is lost.
