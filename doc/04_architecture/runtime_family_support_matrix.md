# Runtime Family Support Matrix

> Authoritative contract for GC/no-GC runtime family implementation.
> Other agents implement against this matrix. Updated 2026-04-04.

## Section 1: Family Classification

| Family | Classification | Dir Exists | Files | Allocation | Mutation | Async | GC | Baremetal | FFI |
|--------|---------------|-----------|-------|------------|----------|-------|----|-----------|-----|
| `common` | **public** | Yes | 799 | heap (default) | immutable preferred | no | n/a (pure) | no | no |
| `nogc_sync_mut` | **public** | Yes | 835 | heap+arena+pool+slab | mutable (`me`) | no | no | no | heavy (SFFI) |
| `nogc_async_mut` | **public** | Yes | 181 | heap | mutable (`me`) | yes | no | no | thread SFFI |
| `gc_async_mut` | **public** | Yes | 46 | GC-managed heap | mutable (`me`) | yes | yes | no | GPU SFFI |
| `nogc_async_immut` | **advanced-scoped** | Yes | 22 | structural sharing | immutable (no `me` on data) | yes (CAS atoms) | no | no | minimal |
| `nogc_async_mut_noalloc` | **public** | Yes | 90 | stack only (no heap) | mutable (`me`) | yes (embedded) | no | **yes** | bare SFFI |
| `gc_sync_immut` | **internal-only** | No | 0 | not implemented | n/a | n/a | n/a | n/a | n/a |
| `gc_sync_mut` | **internal-only** | No | 0 | not implemented | n/a | n/a | n/a | n/a | n/a |
| `nogc_sync_immut` | **internal-only** | No | 0 | not implemented | n/a | n/a | n/a | n/a | n/a |

### Classification criteria

- **public**: Directory exists, has `__init__.spl` with exports, referenced in module loader search path, has test coverage.
- **advanced-scoped**: Directory exists with code but NOT in interpreter module loader search order; limited test coverage; requires explicit qualified imports.
- **internal-only**: No directory exists. Tests may reference the name aspirationally but no implementation.

---

## Section 2: Per-Family Contract

### 2.1 `common` (799 files)

- **Allocation model**: Default heap allocation via GC-managed references (inherits project default). Pure-function oriented.
- **Mutation rules**: Prefers immutable `val` bindings. No `me` methods expected on core data types. Utility functions are stateless.
- **Async support**: None. Synchronous-only pure functions.
- **Concurrency model**: Thread-safe by nature (no mutable state). Functions are reentrant.
- **FFI expectations**: None. Pure Simple code only.
- **Target suitability**: All targets (hosted, embedded conceptually, but not baremetal-validated). Serves as shared foundation imported by all other families.
- **Key modules**: `iterator/`, `text/`, `math/`, `encoding/`, `crypto/`, `json/`, `sdn/`, `regex/`, `color/`, `date/`, `uuid/`.

### 2.2 `nogc_sync_mut` (835 files -- largest family)

- **Allocation model**: Heap allocation via unique pointers (RAII ownership). Also provides explicit `Allocator` types: `SystemAllocator`, `ArenaAllocator`, `PoolAllocator`, `SlabAllocator`.
- **Mutation rules**: Mutable via `me` methods. `var` bindings allowed. Full read-write access.
- **Async support**: None. Strictly synchronous.
- **Concurrency model**: Single-threaded mutable. Atomic types (`AtomicI64`, `AtomicBool`) exported but concurrency is caller's responsibility.
- **FFI expectations**: Heavy SFFI. Exports `extern fn rt_*` wrappers for file I/O, process, network, database, TUI, debugger.
- **Target suitability**: Hosted platforms (Linux, macOS, Windows). Not baremetal. The primary "systems programming" family.
- **Key modules**: `io/`, `fs/`, `net/`, `ffi/`, `db_atomic`, `debug`, `allocator`, `gc` (GcHeap implementation), `simd`, `binary_io`, `tui/`.

### 2.3 `nogc_async_mut` (181 files)

- **Allocation model**: Heap allocation via unique pointers. Actor/task heaps with per-actor isolation (`ActorHeap`).
- **Mutation rules**: Mutable via `me` methods. Actors own their state; messages are value-copied.
- **Async support**: Full. `Future`, `Promise`, `Task`, `Executor`, `Scheduler`. Both embedded (`EmbeddedScheduler`) and host (`HostRuntime`) async runtimes.
- **Concurrency model**: Actor model (`Actor`, `ActorMailbox`, `Supervisor`), OTP-style (`GenServer`, `GenEvent`, `GenStatem`), thread pools (`ThreadPool`), channels (`MpscQueue`, `MpmcQueue`).
- **FFI expectations**: Thread SFFI (`thread_create`, `mutex_create`, `condvar_create`). Actor scheduling via SFFI.
- **Target suitability**: Hosted platforms. Embedded async (no-OS) via `EmbeddedScheduler`. Not baremetal-validated.
- **Key modules**: `actor/`, `async`, `async_host`, `async_embedded`, `concurrent`, `gen_server`, `supervisor`, `mailbox`, `thread_pool`, `coroutine`, `generator`.

### 2.4 `gc_async_mut` (46 files)

- **Allocation model**: GC-managed references (shared pointers). GPU device memory via `GpuPtr`, `GpuBuffer`.
- **Mutation rules**: Mutable via `me` methods. GC handles lifetime; no explicit free.
- **Async support**: Implicit via GPU kernel launch/sync model.
- **Concurrency model**: GPU kernel parallelism. Host-side is single-threaded with GPU sync points.
- **FFI expectations**: Heavy GPU SFFI (`gpu_init`, `gpu_alloc`, `gpu_launch`, `gpu_sync`, CUDA/Vulkan bindings). BLAS-like ops (`gpu_gemm`, `gpu_dot`).
- **Target suitability**: Hosted platforms with GPU (CUDA/Vulkan). Requires GC runtime.
- **Key modules**: `gpu` (all GPU operations), `cuda/`, `torch/`, `gpu_runtime/`.

### 2.5 `nogc_async_immut` (22 files -- advanced-scoped)

- **Allocation model**: Structural sharing (persistent data structures). HAMT maps, RRB-tree vectors, cons lists, LLRB trees, prefix tries.
- **Mutation rules**: Data structures are immutable (no `me` methods). Coordination primitives (`Atom`, `Ref`, `VersionedSnapshot`) use `me` for CAS-based mutation.
- **Async support**: Lock-free concurrency via CAS atoms. MVCC snapshots.
- **Concurrency model**: Lock-free immutable data with CAS coordination. Zero-copy actor snapshots.
- **FFI expectations**: Minimal. CAS operations may require SFFI atomics.
- **Target suitability**: Hosted platforms. Designed for concurrent functional programming.
- **Key modules**: `PersistentMap`, `PersistentVec`, `PersistentList`, `PersistentSortedMap`, `PersistentTrie`, `Atom`, `Ref`, `VersionedSnapshot`, `ActorSnapshot`.
- **NOTE**: Not in interpreter module loader search order. Requires explicit `use std.nogc_async_immut.*` imports.

### 2.6 `nogc_async_mut_noalloc` (90 files -- baremetal)

- **Allocation model**: Stack-only. No heap allocation. `alloc_allowed: false` enforced by `BaremetalConfig`.
- **Mutation rules**: Mutable via `me` methods. All data must be stack-allocated or statically allocated.
- **Async support**: Embedded async (cooperative scheduling, no OS).
- **Concurrency model**: Cooperative multitasking on single core. No threads.
- **FFI expectations**: Bare SFFI for hardware access (MMIO, interrupts). Architecture-specific: ARM, ARM64, RISC-V, RISC-V32, x86, x86_64.
- **Target suitability**: Baremetal only. Target triples: `armv7m-none-eabi`, `x86_64-unknown-none`, `riscv64gc-unknown-none-elf`. QEMU-validated.
- **Key modules**: `baremetal/` (arm, arm64, riscv, riscv32, x86, x86_64), `execution/`, `memory/`, `async/`, `collections/`, `qemu/`, `io/`, `math/`, `string/`, `hash/`, `sort/`.
- **Alloc checking**: `src/compiler/80.driver/build/alloc_checker.spl` provides static analysis that scans imports for `@alloc`-annotated modules.

---

## Section 3: Current Proof Status

| Family | Compiler GcMode Enforcement | Interpreter Parity | Stdlib `__init__.spl` | Module Loader Search | Compiled Tests | Gap Summary |
|--------|---------------------------|-------------------|----------------------|---------------------|----------------|-------------|
| `common` | None (inherits project default) | Yes (auto-resolved) | Yes (exports exist) | Yes (3rd priority) | Partial | No `@gc`/`@no_gc` attribute on `__init__.spl` |
| `nogc_sync_mut` | None (convention only) | Yes (2nd priority in search) | Yes (rich exports) | Yes (2nd priority) | Good | No `@no_gc` attribute; largest family but no GC enforcement |
| `nogc_async_mut` | None (convention only) | Yes (1st priority in search) | Yes (rich exports) | Yes (1st priority, default) | Good | No `@no_gc` attribute; default search but no enforcement |
| `gc_async_mut` | None (convention only) | Yes (4th priority in search) | Yes (GPU exports) | Yes (4th priority) | Partial (GPU-specific) | No `@gc` attribute; GC assumed but not compiler-enforced |
| `nogc_async_immut` | None (convention only) | **No** (not in search order) | Yes (version fn only) | **No** | Minimal | Not in interpreter search path; `__init__.spl` exports only a version function |
| `nogc_async_mut_noalloc` | Partial (alloc_checker) | Yes (5th priority in search) | **No** (no root `__init__.spl`) | Yes (5th priority) | Partial (QEMU) | No root `__init__.spl`; has sub-module inits only |
| `gc_sync_immut` | Not implemented | Not implemented | Does not exist | No | None | Aspirational only |
| `gc_sync_mut` | Not implemented | Not implemented | Does not exist | No | Tests exist (`test/unit/lib/gc_sync_mut/`) but no source | Tests reference non-existent family |
| `nogc_sync_immut` | Not implemented | Not implemented | Does not exist | No | None | Aspirational only |

### Compiler enforcement detail

The compiler has two GcMode systems that are **not connected to directory-based families**:

1. **`GcMode` in `gc_config.spl`** (L00.common): Binary enum `{Gc, NoGc}`. Controls pointer semantics (Shared vs Unique). Set via `@no_gc`/`@gc` attributes on modules/files or project config. Emits **warnings** (not errors) on cross-mode boundary calls via `GcBoundaryChecker`.

2. **`GcMode` in `barriers.spl`** (L55.borrow): Separate enum `{StopTheWorld, Incremental, Generational, Concurrent}`. Controls write barrier requirements for GC safety analysis. Used by `GcSafetyAnalyzer` on MIR.

3. **`gc_off` flag** in `CompileOptions`: Boolean flag passed through the compilation pipeline. Affects compile options hash for caching. Does NOT trigger family-specific module resolution.

4. **`alloc_checker.spl`** in `80.driver/build/`: Scans imports for `@alloc` annotations. Only checks a hardcoded list of 5 modules (`string`, `text`, `array`, `path`, `effects`). Does NOT enforce directory-level family contracts.

**Critical gap**: No compiler pass maps directory family names (`nogc_sync_mut`, `gc_async_mut`, etc.) to `GcMode` settings. Family membership is purely a naming convention with no compile-time enforcement.

### Interpreter parity detail

- **Zero GC/runtime-family references** in `src/compiler/95.interp/` (confirmed by exhaustive grep).
- The interpreter module loader in `src/compiler/10.frontend/core/interpreter/module_loader.spl` has a **hardcoded search order**: `nogc_async_mut` > `nogc_sync_mut` > `common` > `gc_async_mut` > `nogc_async_mut_noalloc`.
- `nogc_async_immut` is **excluded** from this search order.
- The interpreter does not check or enforce GcMode at all. It resolves `use std.X` by trying each family directory in order until a file is found.

---

## Section 4: Known Gaps

### Gap 1: No attribute-based family enforcement (Agent 2 -- Compiler)
- **Problem**: No `__init__.spl` in any family directory carries `@no_gc` or `@gc` attributes. Family GcMode is convention only.
- **Impact**: A file in `nogc_sync_mut/` can use GC-managed references without any compiler warning or error.
- **Fix**: Add `@no_gc` to `__init__.spl` in all `nogc_*` families; add `@gc` to `gc_*` families. Wire manifest loader to propagate GcConfig from directory attributes to child modules.

### Gap 2: Interpreter ignores GcMode entirely (Agent 3 -- Interpreter)
- **Problem**: `src/compiler/95.interp/` has zero GcMode references. The interpreter does not check whether a module's GC requirements match its family.
- **Impact**: Code that would fail compiled-mode GC boundary checks passes silently in interpreter mode.
- **Fix**: At minimum, propagate GcConfig from module manifest to interpreter context. Emit warnings on cross-mode calls matching the compiler's `GcBoundaryChecker` behavior.

### Gap 3: `nogc_async_immut` not in interpreter search path (Agent 3/4)
- **Problem**: The interpreter module loader search order omits `nogc_async_immut`. Users cannot `use std.X` to resolve modules from this family.
- **Impact**: The family is effectively invisible in interpreter mode unless explicitly qualified.
- **Fix**: Add `nogc_async_immut` to the interpreter search order (position: after `common`, before `gc_async_mut`).

### Gap 4: `nogc_async_mut_noalloc` missing root `__init__.spl` (Agent 4 -- Stdlib)
- **Problem**: Has sub-module `__init__.spl` files but no root-level one. The `__init__.spl` would normally declare the family's public API surface.
- **Impact**: Wildcard imports (`use std.nogc_async_mut_noalloc.*`) will fail or return nothing.
- **Fix**: Create root `__init__.spl` with appropriate exports from sub-modules.

### Gap 5: `alloc_checker` only covers 5 hardcoded modules (Agent 2 -- Compiler)
- **Problem**: `alloc_checker.spl` only checks `string`, `text`, `array`, `path`, `effects` for `@alloc` annotations. Does not cover the full stdlib.
- **Impact**: Baremetal builds can silently import heap-allocating modules not on the hardcoded list.
- **Fix**: Extend to scan all `use std.*` imports, or integrate with manifest-level capability checking.

### Gap 6: `gc_sync_mut` has tests but no source (Agent 4 -- Stdlib)
- **Problem**: `test/unit/lib/gc_sync_mut/` contains 4 spec files (`gc_root_spec.spl`, `gc_specific_spec.spl`, `ptr_parity_spec.spl`, `rc_spec.spl`) but `src/lib/gc_sync_mut/` does not exist.
- **Impact**: Tests will fail with module-not-found errors. Tests may be testing against `nogc_sync_mut` modules that export GC-related types (e.g., `GcHeap`, `Rc`, `Arc` in `nogc_sync_mut`).
- **Decision needed**: Are these tests intended for a future family, or should they be relocated to `test/unit/lib/nogc_sync_mut/`?

### Gap 7: Two conflicting `GcMode` enums (Agent 2 -- Compiler)
- **Problem**: `gc_config.spl` defines `GcMode {Gc, NoGc}` and `barriers.spl` defines `GcMode {StopTheWorld, Incremental, Generational, Concurrent}`. These are unrelated types with the same name.
- **Impact**: Confusing for developers. Import conflicts if both are used in the same file.
- **Fix**: Rename `barriers.spl`'s enum to `GcStrategy` or `BarrierMode` to distinguish from the family-level GcMode.

### Gap 8: No target preset maps to family (Agent 5 -- Target Presets)
- **Problem**: `BaremetalConfig` sets `alloc_allowed: false` but does not set GcMode or restrict module resolution to `nogc_async_mut_noalloc`.
- **Impact**: A baremetal build could import from any family directory.
- **Fix**: Wire `BaremetalConfig` to set `gc_off: true` and restrict module loader search to `nogc_async_mut_noalloc` + `common` only.

### Gap 9: `nogc_async_immut` exports only a version function (Agent 4 -- Stdlib)
- **Problem**: The root `__init__.spl` exports only `nogc_async_immut_version`. No data structure types are re-exported.
- **Impact**: Users must know exact sub-module paths to use persistent data structures.
- **Fix**: Add exports for core types (`PersistentMap`, `PersistentVec`, `Atom`, `Ref`, etc.) to `__init__.spl`.

### Gap 10: No compiled test coverage for GC boundary enforcement (Agent 6 -- Tests)
- **Problem**: `test/unit/compiler/semantics/gc_safety_spec.spl` and `test/unit/compiler/common/gc_config_spec.spl` exist but test the type definitions, not actual cross-family boundary enforcement.
- **Impact**: Cannot verify that `GcBoundaryChecker` warnings fire when crossing family boundaries.
- **Fix**: Add integration tests that import across families and verify warnings/errors.

---

## Section 5: Early Decisions

### Decision 1: Which runtime families are truly public?

**Answer**: Five families are public based on code evidence:

| Family | Evidence |
|--------|---------|
| `common` | 799 files, in interpreter search path, rich exports |
| `nogc_sync_mut` | 835 files, in interpreter search path, primary systems family |
| `nogc_async_mut` | 181 files, default interpreter search priority, actor/async system |
| `gc_async_mut` | 46 files, in interpreter search path, GPU/ML-specific |
| `nogc_async_mut_noalloc` | 90 files, in interpreter search path, baremetal with QEMU tests |

One family is **advanced-scoped** (exists but not fully integrated): `nogc_async_immut` (22 files, NOT in interpreter search path, minimal `__init__.spl`).

Three families are **not implemented**: `gc_sync_immut`, `gc_sync_mut`, `nogc_sync_immut`. These exist only as aspirational names. `gc_sync_mut` has orphaned test files.

### Decision 2: Is interpreter parity mandatory for all public families?

**Answer**: Yes for the 5 public families, with caveats:
- The interpreter currently achieves module-resolution parity via the hardcoded search order.
- GcMode enforcement parity is NOT present (interpreter has zero GcMode checks).
- **Minimum bar**: Interpreter must resolve modules from all 5 public families (currently true) AND emit warnings on cross-family GcMode mismatches (currently false).
- **Stretch goal**: Full GcBoundaryChecker parity in interpreter mode.
- `nogc_async_immut` should be added to the search order to become fully public.

### Decision 3: Which stdlib differences are intentional vs accidental?

**Intentional differences** (by design):
- `common` has no `me` methods (stateless utility library).
- `nogc_async_immut` data structures return new versions instead of mutating (persistent data design).
- `nogc_async_mut_noalloc` forbids heap allocation (baremetal constraint).
- `gc_async_mut` requires GC runtime (GPU memory management model).

**Accidental differences** (bugs to fix):
- `nogc_async_immut` not in interpreter search order.
- `nogc_async_mut_noalloc` missing root `__init__.spl`.
- `nogc_async_immut.__init__.spl` exports only version function.
- `gc_sync_mut` tests exist without source implementation.
- Duplicate module exports across families (e.g., `io_runtime`, `platform`, `spec`, `log` appear in both `nogc_sync_mut` and root `lib/__init__.spl`).

### Decision 4: Which target presets are authoritative for no-GC?

**Answer**: The baremetal presets in `src/compiler/80.driver/build/baremetal.spl` are the only implemented target presets:

| Preset | Triple | `alloc_allowed` | Implied Family |
|--------|--------|----------------|---------------|
| `BaremetalConfig.arm()` | `armv7m-none-eabi` | `false` | `nogc_async_mut_noalloc` |
| `BaremetalConfig.x86_64()` | `x86_64-unknown-none` | `false` | `nogc_async_mut_noalloc` |
| `BaremetalConfig.riscv()` | `riscv64gc-unknown-none-elf` | `false` | `nogc_async_mut_noalloc` |

The `gc_off` flag in `CompileOptions` provides a global no-GC switch but does NOT map to a specific family. There are no presets for hosted no-GC targets (i.e., no preset says "use `nogc_sync_mut` as default family").

**Gap**: Target presets should explicitly set the default family for module resolution, not just `alloc_allowed`.

### Decision 5: What counts as "complete" for weakest families?

**For `nogc_async_immut`** (advanced-scoped, weakest existing):
- [ ] Add to interpreter module loader search order
- [ ] Export core types from `__init__.spl`
- [ ] Add `@no_gc` attribute to `__init__.spl`
- [ ] Add at least 5 unit tests covering core data structures
- [ ] Verify CAS atom operations work in compiled mode

**For `gc_sync_mut`** (not implemented, has orphaned tests):
- **Decision**: Either create the family directory with GC+sync+mutable semantics, OR relocate orphaned tests to `nogc_sync_mut` and formally remove `gc_sync_mut` from the plan.
- **Recommendation**: Relocate tests. The `nogc_sync_mut` family already exports `GcHeap`, `GcConfig`, `Rc`, `Arc` -- these cover the GC-managed reference-counted types that `gc_sync_mut` tests appear to need.

**For `gc_sync_immut` and `nogc_sync_immut`** (not implemented, no tests):
- **Decision**: Mark as "deferred" and do not create directories. No code or tests reference them.
- **Rationale**: The existing 6 families cover all current use cases. Adding sync+immutable variants provides marginal value since `common` already serves as the pure/immutable foundation.

---

## Appendix A: File Inventory by Family

| Family | `.spl` Files | Sub-modules | `__init__.spl` Exports |
|--------|-------------|-------------|----------------------|
| `common` | 799 | iterator/, text/, math/, encoding/, crypto/, json/, sdn/, regex/, color/, date/, uuid/, ... | Via parent `src/lib/__init__.spl` |
| `nogc_sync_mut` | 835 | io/, fs/, net/, ffi/, db/, debug/, allocator/, gc/, simd/, tui/, spec/, ... | Rich (allocator, array, atomic, binary_io, conf, db, debug, fs, gc, io, net, path, perf, platform, rc, simd, spec, ...) |
| `nogc_async_mut` | 181 | actor/, async, concurrent, gen_server, supervisor, mailbox, thread_pool, coroutine, generator, ... | Rich (actors, async, concurrent, effects, generators, monitors, supervisors, threads) |
| `gc_async_mut` | 46 | gpu, cuda/, torch/, gpu_runtime/ | GPU operations (gpu_*, GpuDevice, GpuBuffer, etc.) |
| `nogc_async_immut` | 22 | (planned: persistent data structures) | `nogc_async_immut_version` only |
| `nogc_async_mut_noalloc` | 90 | baremetal/ (6 archs), execution/, memory/, async/, collections/, qemu/, io/, math/, string/, hash/, sort/ | No root init; sub-module inits exist |

## Appendix B: Compiler GC Infrastructure Map

| File | Layer | Purpose | Connected to Families? |
|------|-------|---------|----------------------|
| `src/compiler/00.common/gc_config.spl` | L00 | `GcMode {Gc, NoGc}`, `GcConfig`, provenance tracking | No (attribute-based, not directory-based) |
| `src/compiler/00.common/gc_boundary.spl` | L00 | `GcBoundaryChecker`, cross-mode call/return/conversion warnings | No (checks attribute GcMode, not family) |
| `src/compiler/99.loader/module_resolver/manifest.spl` | L99 | Parses `@no_gc`/`@gc` from `__init__.spl` attributes, propagates to `ChildModule.gc_config` | **Potential**: manifest already reads `@no_gc`/`@gc` but no family `__init__.spl` uses them |
| `src/compiler/55.borrow/gc_analysis/barriers.spl` | L55 | Write barrier analysis (`GcMode {StopTheWorld, Incremental, Generational, Concurrent}`) | No (MIR-level analysis, separate GcMode enum) |
| `src/compiler/55.borrow/gc_analysis/mod.spl` | L55 | `GcSafetyAnalyzer`, root tracking, escape analysis | No (operates on MIR, not module families) |
| `src/compiler/80.driver/build/alloc_checker.spl` | L80 | `@alloc`/`@no_alloc` annotation checker (5 hardcoded modules) | Weak (checks annotations but only 5 modules) |
| `src/compiler/80.driver/build/baremetal.spl` | L80 | `BaremetalConfig` with `alloc_allowed: false`, target triples | Indirect (implies `nogc_async_mut_noalloc` but does not enforce) |
| `src/compiler/00.common/driver_core_types.spl` | L00 | `CompileOptions.gc_off` flag | No (global toggle, not per-family) |
| `src/compiler/10.frontend/core/interpreter/module_loader.spl` | L10 | Hardcoded family search order for `use std.*` resolution | **Yes** (only place families are explicitly listed) |

## Appendix C: Test Coverage Map

| Test File | Tests Family | Type |
|-----------|-------------|------|
| `test/unit/compiler/common/gc_config_spec.spl` | GcMode/GcConfig types | Unit |
| `test/unit/compiler/semantics/gc_safety_spec.spl` | GC safety analysis | Unit |
| `test/feature/usage/gc_managed_default_spec.spl` | GC managed default behavior | Feature |
| `test/feature/lib/gc_parity/gc_module_loader_spec.spl` | GC module loader parity | Feature |
| `test/feature/lib/gc_parity/gc_sync_mut_spec.spl` | gc_sync_mut parity | Feature |
| `test/system/features/gc_system_spec.spl` | GC system-level | System |
| `test/lib/std/unit/gc_spec.spl` | GC stdlib unit | Unit |
| `test/unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.spl` | GPU borrowed views | Unit |
| `test/unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.spl` | CUDA ownership | Unit |
| `test/unit/lib/gc_async_mut/torch/gc_*_spec.spl` (3 files) | Torch GC integration | Unit |
| `test/unit/lib/gc_sync_mut/gc_root_spec.spl` | GC roots (orphaned) | Unit |
| `test/unit/lib/gc_sync_mut/gc_specific_spec.spl` | GC specifics (orphaned) | Unit |
| `test/unit/compiler/target_presets_spec.spl` | Target presets | Unit |
| `test/system/baremetal_test_runner_spec.spl` | Baremetal test runner | System |
