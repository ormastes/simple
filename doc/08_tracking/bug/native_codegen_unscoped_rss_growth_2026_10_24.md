# Native codegen retains ~29 MB per module: no transient scope (2026-10-24)

Bug id: `native_codegen_unscoped_rss_growth_2026_10_24`
Related: `borrow_check_unscoped_rss_growth_2026_10_24.md` (the same defect class in
borrow check), `mir_phase_rss_retention_2026_10_24.md`.

## Symptom
In one-binary `native-build --backend cranelift`, worker RSS grows linearly for each
module codegen compiles, and none of it comes back. On the 204-module probe the codegen
phase OOM-killed the worker under a 16G cgroup after 147 objects. At the full 1471-module
Phase 3 size this phase dominates.

## Attribution (204-module probe `pa.spl`, run `scratchpad/cgmem/run-before`)
- Producer: `bootstrap-p2shard-3/stage2/.../simple` (sha256 prefix `d8a843282b94d94b`).
  This is the old producer, without the borrow-scope fix.
- Settings: `MemoryMax=16G`, 1 s sampling, `SIMPLE_COMPILER_PHASE_PROFILE=1`, and a
  fresh `--cache-dir`, so every module is a cache miss.
- Launcher: `scratchpad/cgmem/cg.sh` (derived from `mirmem/mb.sh`). Each second it
  also counts the `*.o` files in the cache.
- Borrow check takes worker RSS from 3.6 GB to 10.0 GB. That is the separate borrow bug.
- `native_compile`: `172 uncached module(s), concurrency=1`. The BackendSession path is
  the one in use (log: `backend session AOT result rejected` for `lib.common.math.math`).
- Worker RSS against objects written: 10274 MiB at 2 objects, then 14439 MiB at
  147 objects, after 44 s, when the run was OOM-killed (rc=143).
  - That is **+4165 MiB over 145 modules = ~28.7 MiB/module**. The growth is linear
    with no plateau.
- The 148 objects together are 9.2 MiB on disk (63 KiB on average). Object bytes are
  copied three times as `[u8]`: the adapter read, the session record copy
  (`session_authority_v2.spl:418`) and the projection copy (`:546`). Even counting all
  three copies, that is well under 5% of the growth.
  - The rest is per-module backend scratch: `lower_mir_storage_project_fields_v1`, the
    `optimize_module_for_backend` MIR copy, and Cranelift translation state
    (`func_handles` and per-function dicts).

## Cause
`_compile_frozen_module_capsule` calls `_compile_selected_module` (`driver_aot_native_output.spl:3836`
at 8404ef6c1d1, `:3841` after this fix) with no transient
scope (`src/compiler/80.driver/driver_aot_native_output.spl`, the `match
_compile_selected_module(...)` in `_compile_frozen_module_capsule`). The runtime is no-GC.
An allocation comes back only through `rt_transient_array_scope_end`. So everything the
backend allocates per module lives until the process exits.

Findings on the other questions:
- **Cranelift module handles are already freed.** `cranelift_free_module` runs on every
  path in `70.backend/backend/cranelift_codegen_adapter.spl` (`cranelift_new_aot_for_request_v2`,
  `compile_module`, `cranelift_compile_module_direct`). The native side is not the leak.
- **MIR eviction cannot help.** `CompileContext.evict_mir_module`
  (`80.driver/driver_types.spl:1404`) only does `mir_modules.remove(name)`. The MIR was
  promoted to immortal during lowering, and removing it from the dict frees nothing.
  Go-to-end already evicts after the batch, at the end of the `uncached_names` block.
  Moving that per-module would save 0 bytes, so it was not done.
- **Object byte arrays are not retained in a driver collection.** The driver keeps only
  paths (`object_files`, `library_members`, `native_staged_codegen.module_objects`). The
  session's `result_release_v2` drops its record, but nothing frees it, so the copies
  leaked unscoped. They are covered by the scope below.

## Fix
`_compile_selected_module_scoped_v1` (same file):
1. Begin a scope.
2. Run `_compile_selected_module`.
3. Inside the arm that binds the payload, pause the scope.
4. Promote only the object-path / error text, plus the backend session lease. Its
   authority records (`uses`, `results`, `kept`, `retained_bytes`) are mutated during
   the compile.
5. End the scope.

Fallbacks:
- If an outer scope is live, the scope is refused. The module then compiles unscoped,
  with a loud `[codegen-scope] WARNING`.
- If promotion fails, the module fails closed with `codegen-scope-promotion-failed`.
  The module is not re-emitted, because its object is already on disk.

Also: `auto_vectorize_target_level()` is now resolved once before the codegen loop. Its
`_cached_level` memo is a module-level text global. If it were first assigned inside a
scope, the scope's end would free it.

Why verdicts and object bytes do not change:
- The MIR input was promoted before the scope and is only read.
  `capsule.identity_valid()` re-hashes it after codegen and fails on any change.
- Every capsule receipt, cache, outcome and publication write stays outside the scope,
  in the caller.
- Module-level state written inside the scope was audited across `70.backend/backend`,
  `backend_plugin`, `60.mir_opt` and the driver helpers:
  - `_cached_level`: pre-resolved before the loop.
  - The K1 static backend table: installed at composition, before codegen.
  - `simd_opt_metadata.g_provider_report.events`: write-only, never read by the compiler.
  - `compiler_work_counters_v1`: updated before the scope opens.

## Expected
About 28 MiB/module saved, which is about 40 GB at 1471 modules. One large module still
peaks inside its own scope. The fix bounds the cumulative growth, not that single-module
peak.

**AFTER numbers are PENDING a Stage 2 rebuild.** The fix lives in compiler source, and
the current producer is prebuilt. After the rebuild:
- Re-run `cg.sh after` and compare RSS per object.
- A `[codegen-scope] WARNING` line means scoping was refused and the saving is lost.

## Regression: v1 scope placement (Stage 2 p2shard-5, 2026-10-24)
The first placement opened the scope in `_compile_selected_module_scoped_v1`, around the
whole driver call. With `SIMPLE_CODEGEN_MODULE_SCOPE=1`, the rejected candidate
(`stage2/.../simple.rejected`, sha256 `f3498fc086b6a183`) fails Stage 2 sanity on
`compiler.bootstrap_admission.p2_add`:
- `[codegen-scope] WARNING promotion failed (paused=true kept=true session=false ended=true)`.
- The module then fails closed with `codegen-scope-promotion-failed (object written)`.
- The worker then exits with SIGSEGV (-139).
- The failure is reproduced locally with `scratchpad/cgmem/p2.sh red <candidate>`
  (rc=117, same lines).

Cause:
- On the BackendSession path, `compile_owned_aot_into_path_v2` mutates the persistent
  `BackendSessionAuthorityV2` *inside* that scope. It acquires a use, pushes the result
  record with copied bytes, rebuilds `results` as `kept`, writes `record.session =
  retained`, and releases the use.
- Promotion cannot rescue those writes:
  - `rt_transient_heap_promote` (`runtime_native.c`) accepts a root only if the root is
    transient-owned or registered-immortal. The long-lived lease graph is neither, so it
    returns 0.
  - Even with an accepted root, `core_transient_add_child` treats any non-transient
    node as a leaf. Scope-allocated children under a persistent parent are never reached.
- Scope end therefore freed records still linked into the authority. The next authority
  access, here the session close after the failed module, read freed memory and crashed.
  The exact faulting frame was not captured; this is inferred.

Fix v2: `compile_module_with_backend_scoped_v1` (`70.backend/backend/backend_helpers.spl`).
- It wraps only the pure `compile_module_with_backend_target_cpu_storage_bindings` call:
  storage lowering, the MIR optimization copy, Cranelift translation and the object
  byte read.
- It promotes only the returned `Result<CompiledModule, CompileError>`. That is a
  registered enum whose payload is entirely scope-allocated.
- Callers:
  - `BuiltinBackendAdapter.compile_aot_module`, the session path. Every authority
    mutation now happens outside the scope.
  - The driver's non-session `_finish_selected_module_compile` call.
- The driver-level scope is removed.
- The Cranelift K1 port builds a fresh adapter on each run, so no backend state
  persists across modules.
- Still opt-in with `SIMPLE_CODEGEN_MODULE_SCOPE=1`.
- The per-module saving now excludes the session's own result-record byte copies
  (2 x object size), which are small next to the ~28 MiB/module of scratch.

Fix v2 is UNVERIFIED pending a Stage 2 rebuild: `p2.sh green <new candidate>` must
exit 0 with no `[codegen-scope]` line. Then re-run `cg.sh after`.
