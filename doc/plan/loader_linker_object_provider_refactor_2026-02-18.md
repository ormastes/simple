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
- Prepass accepts SMF/LSM inputs → temp .o via provider, then native link (mold/cc).
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
