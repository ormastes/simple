# Loader/Linker Object Provider Refactor (2026-02-18)

Goal: make loader + linker actually load/execute SMFs by unifying module access (SmfGetter + ObjTaker), adding real exec-memory mapping, and driving the native linker through SMF-aware inputs. Deployment coverage tests come last.

## Phases

1) **Object Provider Unification**
- Build `object_provider` (wrap SmfGetter + ObjTaker) with a shared cache.
- API: locate modules, emit objects (with optional type args), surface metadata.
- Tests: cache hit/miss unit tests; missing-module error path.

2) **Executable Memory Backing**
- Replace mmap stubs with FFI (mmap/munmap/mprotect/msync/mlock); keep RW→RX and icache flush.
- Exec arena allocator shared by loader.
- Tests: integration exec-memory roundtrip; oversize allocation error.

3) **Loader Execution Path**
- Loader maps SMF via provider, installs symbols into exec arena, sets real addresses; resolves generics via provider.
- Hot-reload reuses provider cache.
- Tests: load+execute fixture function; generic instantiation; hot-reload changed return value.

4) **SMF-Aware Linker Wrapper**
- Prepass accepts SMF/LSM inputs → temp .o via provider (ObjTaker-backed), then native link (mold/cc).
- Library support reuses provider instance.
- Build pipeline calls this instead of raw `mold` on .smf.
- Tests: link/execute small SMF binary; library resolution case.

5) **Backend Selection + PIC Handling**
- Provider honors LLVM vs Cranelift tags; reject or patch non-PIC.
- Tests: backend-switch unit covering release vs debug choice.

6) **Deployment Coverage (@deployment_coverage)**
- New spec grouping the integration tests; register coverage targets (loader, linker_wrapper, obj_taker).
- Run after other tests; thresholds start modest (e.g., 50% branch).

## Immediate next steps (Phase 2 kickoff)
- Implement real mmap FFI backing in `compiler_shared/loader/smf_mmap_native.spl` and wire an exec arena helper.
- Add exec-memory integration test stub (to be enabled once FFI lands).
- Add `--fixed-be` CLI toggle to force a fixed backend (alias to LLVM) when running builds/tests during this refactor so we can validate with a stable codegen path.
- Next: replace temporary SMF-to-.o assembly shim with ObjTaker-backed object emission (one or more symbols), and thread provider through linker_wrapper_lib_support for library resolution.

## Progress (2026-02-18 evening)
- ObjectProvider now caches SMF/object bytes, exposes `get_reader`/`get_exported_code`, and is threaded into loader + linker wrapper.
- ModuleLoader prefers provider-backed readers so .lsm modules can be loaded without filesystem copies.
- Linker wrapper converts SMF/LSM inputs via provider (object bytes first, ObjTaker-backed code fallback via shared object_emitter) and fixes temp-dir cleanup.
- Deployment coverage spec extended to include object_provider and smf bundle fast-path.
- Library-aware resolution now shares provider and can assemble missing objects from exported units.
- Shared `object_emitter` now writes ELF64 relocatable objects directly (x86_64, PIC) and falls back to clang.
- Shared emitter now supports x86_64 + aarch64; unit spec added.
- Next: extend object writer to Mach-O, add relocations where needed, and tighten coverage thresholds.

## Detailed plan + implementation update (shared object mapper)

1) Shared mapper core (`SharedExecMapper`) in `compiler_shared/loader`.
- Status: done
- Provides one mapping API for both loader and JIT:
  - `map_symbol(owner_id, symbol, code, allow_replace)`
  - `lookup(symbol)`
  - `unmap_symbol(symbol)`
  - `unmap_owner(owner_id)`
  - `stats()`
- Ownership model:
  - loader symbols keyed by module path owner
  - JIT symbols keyed by `__jit__` owner

2) Loader wiring (`compiler_shared/loader/module_loader.spl`).
- Status: done
- `moduleloader_allocate_exec` now delegates to `SharedExecMapper`.
- module load path maps with owner=`module_path`.
- JIT fallback path maps with owner=`__jit__` only when JIT did not return pre-mapped address.
- unload path now releases all owner mappings via `unmap_owner(path)`.
- Loader calls the mapper through `self.jit.exec_mapper`, so loader + JIT share one mapper instance per loader runtime.

3) JIT wiring (`compiler/loader/jit_instantiator.spl`).
- Status: done
- Removed local executable-memory stubs from active flow.
- JIT compile success path now maps code through `SharedExecMapper` with replace enabled.
- JIT cache/symbol table continue to track resolved function pointers.

4) Compatibility adapter.
- Status: done
- Added `compiler/loader/object_mapper.spl` re-export so compiler-side code can import shared mapper API via existing loader namespace.

5) Validation plan.
- Status: done (interpreter-mode load checks)
- Add unit tests for:
  - duplicate map rejection when `allow_replace=false`
  - replace behavior when `allow_replace=true`
  - owner-based unmap correctness
- Added `test/unit/compiler/loader/object_mapper_spec.spl`.
- Ran targeted checks:
  - `bin/simple test test/unit/compiler/loader/object_mapper_spec.spl`
  - `bin/simple test test/unit/compiler/loader/jit_instantiator_spec.spl`
  - `bin/simple test test/unit/compiler/loader/module_loader_spec.spl`

## Open issues and better-way follow-up

1) Owner attribution for JIT-compiled module symbols.
- Status: fixed
- JIT compile path now maps module-origin symbols with owner=`smf_path`.
- `__jit__` remains fallback owner when no mapped owner record exists.

2) Global symbol table cleanup on unload.
- Status: fixed
- Unload now removes all `global_symbols` entries whose owner path matches the unloaded module.
- Unload also drops matching JIT cache entries to avoid stale cache/symbol-table pointers.

3) Policy isolation.
- Status: fixed
- Added policy facades over `SharedExecMapper`:
  - `LoaderMapper` for strict ownership + unload semantics
  - `JitMapper` for replace-on-recompile + owner defaults
- Loader module allocation now goes through `LoaderMapper`; JIT mapping goes through `JitMapper`.

4) Added regression coverage for wrapper behavior.
- Status: fixed
- `object_mapper_spec` now covers:
  - loader replace policy reject/allow
  - JIT default owner fallback when owner id is empty
- `module_loader_spec` now covers:
  - JIT mapper owner propagation into `global_symbols`
  - unload clearing module-owned JIT mapping + JIT cache entries
