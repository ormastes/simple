# Runtime Family Support Matrix

> Authoritative contract for GC/no-GC runtime family implementation.
> Other agents implement against this matrix. Updated 2026-05-14.

## Section 1: Family Classification

| Family | Classification | Dir Exists | Files | Allocation | Mutation | Async | GC | Baremetal | FFI |
|--------|---------------|-----------|-------|------------|----------|-------|----|-----------|-----|
| `common` | **public** | Yes | 1166 | heap (default) | immutable preferred | no | n/a (pure) | no | no |
| `nogc_sync_mut` | **public** | Yes | 1434 | heap+arena+pool+slab | mutable (`me`) | no | no | no | heavy (SFFI) |
| `nogc_async_mut` | **public** | Yes | 1688 | heap | mutable (`me`) | yes | no | no | thread SFFI |
| `gc_async_mut` | **public** | Yes | 914 | GC-managed heap | mutable (`me`) | yes | yes | no | GPU SFFI |
| `nogc_async_immut` | **advanced-scoped** | Yes | 22 | structural sharing | immutable (no `me` on data) | yes (CAS atoms) | no | no | minimal |
| `nogc_async_mut_noalloc` | **public** | Yes | 128 | stack only (no heap) | mutable (`me`) | yes (embedded) | no | **yes** | bare SFFI |
| `gc_sync_mut` | **advanced-scoped** | Yes | 812 | GC-managed heap | mutable (`me`) | sync facade | yes | no | via `gc_async_mut` |
| `gc_async_immut` | **advanced-scoped** | Yes | 22 | GC-managed heap facade over structural sharing | immutable | async facade | yes | no | via `nogc_async_immut` |
| `gc_sync_immut` | **advanced-scoped** | Yes | 22 | GC-managed heap facade over structural sharing | immutable | sync facade | yes | no | via `gc_async_immut` |
| `nogc_sync_immut` | **advanced-scoped** | Yes | 22 | structural sharing | immutable | sync facade | no | no | via `nogc_async_immut` |

### Classification criteria

- **public**: Directory exists, has `__init__.spl` with exports, referenced in module loader search path, has test coverage.
- **advanced-scoped**: Directory exists with code and a root export surface, but still has limited test coverage or incomplete runtime/compiler enforcement for public-family guarantees.
- **internal-only**: Reserved label for future names with no directory or production contract. No current family in this matrix uses it.

---

## Section 2: Per-Family Contract

### 2.1 `common` (1166 files)

- **Allocation model**: Default heap allocation via GC-managed references (inherits project default). Pure-function oriented.
- **Mutation rules**: Prefers immutable `val` bindings. No `me` methods expected on core data types. Utility functions are stateless.
- **Async support**: None. Synchronous-only pure functions.
- **Concurrency model**: Thread-safe by nature (no mutable state). Functions are reentrant.
- **FFI expectations**: None. Pure Simple code only.
- **Target suitability**: All targets (hosted, embedded conceptually, but not baremetal-validated). Serves as shared foundation imported by all other families.
- **Key modules**: `iterator/`, `text/`, `math/`, `encoding/`, `crypto/`, `json/`, `sdn/`, `regex/`, `color/`, `date/`, `uuid/`.

### 2.2 `nogc_sync_mut` (1434 files -- largest canonical family)

- **Allocation model**: Heap allocation via unique pointers (RAII ownership). Also provides explicit `Allocator` types: `SystemAllocator`, `ArenaAllocator`, `PoolAllocator`, `SlabAllocator`.
- **Mutation rules**: Mutable via `me` methods. `var` bindings allowed. Full read-write access.
- **Async support**: None. Strictly synchronous.
- **Concurrency model**: Single-threaded mutable. Atomic types (`AtomicI64`, `AtomicBool`) exported but concurrency is caller's responsibility.
- **FFI expectations**: Heavy SFFI. Exports `extern fn rt_*` wrappers for file I/O, process, network, database, TUI, debugger.
- **Target suitability**: Hosted platforms (Linux, macOS, Windows). Not baremetal. The primary "systems programming" family.
- **Key modules**: `io/`, `fs/`, `net/`, `ffi/`, `db_atomic`, `debug`, `allocator`, `gc` (GcHeap implementation), `simd`, `binary_io`, `tui/`.

### 2.3 `nogc_async_mut` (1688 files)

- **Allocation model**: Heap allocation via unique pointers. Actor/task heaps with per-actor isolation (`ActorHeap`).
- **Mutation rules**: Mutable via `me` methods. Actors own their state; messages are value-copied.
- **Async support**: Full. `Future`, `Promise`, `Task`, `Executor`, `Scheduler`. Both embedded (`EmbeddedScheduler`) and host (`HostRuntime`) async runtimes.
- **Concurrency model**: Actor model (`Actor`, `ActorMailbox`, `Supervisor`), OTP-style (`GenServer`, `GenEvent`, `GenStatem`), thread pools (`ThreadPool`), channels (`MpscQueue`, `MpmcQueue`).
- **FFI expectations**: Thread SFFI (`thread_create`, `mutex_create`, `condvar_create`). Actor scheduling via SFFI.
- **Target suitability**: Hosted platforms. Embedded async (no-OS) via `EmbeddedScheduler`. Not baremetal-validated.
- **Key modules**: `actor/`, `async`, `async_host`, `async_embedded`, `concurrent`, `gen_server`, `supervisor`, `mailbox`, `thread_pool`, `coroutine`, `generator`.

### 2.4 `gc_async_mut` (914 files)

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
- **NOTE**: In interpreter module loader search order, but still advanced-scoped because compiled/runtime coverage is limited.

### 2.6 Compatibility facade families

`gc_sync_mut`, `gc_async_immut`, `gc_sync_immut`, and `nogc_sync_immut` are
compatibility families, not independent backend owners.

- `gc_sync_mut` mirrors tracked `gc_async_mut` modules and exports those modules
  as the synchronous GC compatibility surface.
- `gc_async_immut` and `nogc_sync_immut` mirror `nogc_async_immut` so immutable
  collection APIs exist in GC-async and no-GC-sync configurations without
  duplicating persistent-data-structure logic.
- `gc_sync_immut` mirrors `gc_async_immut`, preserving the same GC immutable API
  shape for sync configurations.
- Backend ownership remains in the existing no-GC async/no-GC sync or pure
  immutable modules. The facade families do not declare runtime hooks.

These families are advanced-scoped until runtime coverage and enforcement prove
the remaining promotion gaps, including manifest-backed capability checks and
sync-wrapper decisions.

### 2.6.1 Backend Routing Policy

The production ownership rule is behavioral, not name-only:

- Async-visible compatibility APIs route through `nogc_async_mut` when the
  no-GC async family has an API-preserving surface.
- Sync-only or blocking runtime ownership remains in `nogc_sync_mut` when
  wrapping it in `nogc_async_mut` would only add a scheduler dependency without
  changing observable behavior.
- `nogc_async_mut` may expose facade modules over `nogc_sync_mut` for
  synchronous FFI boundaries. Those facades must not wildcard-export
  runtime-hook owners; `scripts/audit/runtime_backend_boundaries.py` keeps the
  wildcard-owner scan at zero.
- `gc_async_mut` facades prefer matching `nogc_async_mut` surfaces first. A
  direct `nogc_sync_mut` export is allowed only for pure or synchronous APIs
  that do not have an async-visible contract, and runtime-hook-owner wildcard
  exports are blocked by the same audit.
- `gc_sync_mut` is a compatibility facade over `gc_async_mut`, not a separate
  sync backend. It stays advanced-scoped until selected APIs prove whether they
  need real blocking wrappers.

### 2.7 `nogc_async_mut_noalloc` (128 files -- baremetal)

- **Allocation model**: Stack-only. No heap allocation. Baremetal target presets restrict `allowed_families` to `nogc_async_mut_noalloc` plus `common`.
- **Mutation rules**: Mutable via `me` methods. All data must be stack-allocated or statically allocated.
- **Async support**: Embedded async (cooperative scheduling, no OS).
- **Concurrency model**: Cooperative multitasking on single core. No threads.
- **FFI expectations**: Bare SFFI for hardware access (MMIO, interrupts). Architecture-specific: ARM, ARM64, RISC-V, RISC-V32, x86, x86_64.
- **Target suitability**: Baremetal only. Target triples: `armv7m-none-eabi`, `x86_64-unknown-none`, `riscv64gc-unknown-none-elf`. QEMU-validated.
- **Key modules**: `baremetal/` (arm, arm64, riscv, riscv32, x86, x86_64), `execution/`, `memory/`, `async/`, `collections/`, `qemu/`, `io/`, `log/`, `math/`, `string/`, `hash/`, `sort/`.
- **Alloc checking**: target family filtering plus `dependency_boundary_spec` prevent direct noalloc imports from allocating runtime families, explicit noalloc `@alloc` markers, host allocation APIs, and unsafe reachable imports through helper modules; compiler-owned manifest/capability scanning remains partial.

---

## Section 3: Current Proof Status

| Family | Compiler GcMode Enforcement | Interpreter Parity | Stdlib `__init__.spl` | Module Loader Search | Compiled Tests | Gap Summary |
|--------|---------------------------|-------------------|----------------------|---------------------|----------------|-------------|
| `common` | None (inherits project default) | Yes (auto-resolved) | Yes (exports exist) | Yes (5th priority) | Partial | Neutral shared family; no `@gc`/`@no_gc` attribute |
| `nogc_sync_mut` | `@no_gc` on root `__init__.spl`; family-prefix semantic warnings | Yes (4th priority in search, boundary warnings) | Yes (rich exports) | Yes (4th priority) | Good | Root attribute and direct-import boundary checks present; full manifest-to-GcMode enforcement remains partial |
| `nogc_async_mut` | `@no_gc` on root `__init__.spl`; family-prefix semantic warnings | Yes (1st priority in search, boundary warnings) | Yes (rich exports) | Yes (1st priority, default) | Good | Root attribute and direct-import boundary checks present; full manifest-to-GcMode enforcement remains partial |
| `gc_async_mut` | `@gc` on root `__init__.spl`; parser accepts module-level GC attributes before export-only roots | Yes (6th priority in search) | Yes (GPU exports) | Yes (6th priority) | Partial (GPU-specific) | Root attribute and direct-import boundary checks present; full manifest-to-GcMode enforcement remains partial |
| `nogc_async_immut` | `@no_gc` on root `__init__.spl`; family-prefix semantic warnings | Yes (2nd priority in search, boundary warnings) | Yes (persistent structures, Atom/Ref, combinators) | Yes (2nd priority) | Direct native | Resolution and root exports fixed; persistent-structure facade coverage is broad and direct coordination/CAS native coverage passes, but manifest-backed enforcement remains a promotion gap |
| `nogc_async_mut_noalloc` | `@no_gc` on root `__init__.spl`; direct and reachable unsafe imports plus explicit `@alloc` markers blocked by regression | Yes (10th priority in search, boundary warnings) | Yes (baremetal/noalloc exports) | Yes (10th priority) | Partial (QEMU); check-clean under full-family `simple check` | Root export surface exists; compiler-owned capability enforcement remains partial |
| `gc_sync_mut` | `@gc` on root `__init__.spl`; facade-only | Recognized by interpreter family extraction (8th priority) | Yes (facade root) | Yes (8th priority) | Minimal | Facade over `gc_async_mut`; no independent sync runtime semantics yet |
| `gc_async_immut` | `@gc` on root `__init__.spl`; facade-only | Recognized by interpreter family extraction (7th priority) | Yes | Yes (7th priority) | Broad facade | Native facade resolution passes; the 31-spec native immutable facade batch covers root `Atom`, `VersionedSnapshot`, pmap traversal, pure combinators, root `PersistentList`, partial `PersistentVec`, committed-path `PersistentMap`, `PersistentSet`, package-level `PersistentTrie`, and typed plus untyped chained root-facade `PersistentTrie` behavior without warning/stub output |
| `gc_sync_immut` | `@gc` on root `__init__.spl`; facade-only | Recognized by interpreter family extraction (9th priority) | Yes | Yes (9th priority) | Broad facade | Native facade resolution plus the 31-spec native immutable facade batch pass through the GC async immutable facade without warning/stub output |
| `nogc_sync_immut` | `@no_gc` on root `__init__.spl`; facade-only | Recognized by interpreter family extraction (3rd priority) | Yes | Yes (3rd priority) | Broad facade | Native facade resolution plus the 31-spec native immutable facade batch pass through the no-GC async immutable backend without warning/stub output |

### Compiler enforcement detail

The compiler has one family-level `GcMode` plus a separate barrier-analysis `GcStrategy`:

1. **`GcMode` in `gc_config.spl`** (L00.common): Binary enum `{Gc, NoGc}`. Controls pointer semantics (Shared vs Unique). Set via `@no_gc`/`@gc` attributes on modules/files or project config. Emits **warnings** (not errors) on cross-mode boundary calls via `GcBoundaryChecker`.

2. **`GcStrategy` in `barriers.spl`** (L55.borrow): Separate enum `{StopTheWorld, Incremental, Generational, Concurrent}`. Controls write barrier requirements for GC safety analysis. Used by `GcSafetyAnalyzer` on MIR.

3. **`gc_off` flag** in `CompileOptions`: Boolean flag passed through the compilation pipeline. Affects compile options hash for caching and target presets.

4. **Runtime family manifest checks** in `src/compiler/35.semantics/gc_boundary_check.spl`: `RUNTIME_FAMILY_MANIFEST` records each stdlib family rank, GC mode, allocation behavior, and noalloc status. `check_gc_boundary_imports()` preserves warning output for compatibility, while `check_runtime_family_import_violations()` returns hard violations from the same manifest-backed model. The Rust `simple check` lint path mirrors the same family set, ranks, GC/noalloc rules, and reason strings so the production checker reports manifest-equivalent diagnostics. Target-restricted or CI gates can pass `--deny-gc-boundary` / `--strict-runtime-family` to promote the same diagnostics to hard errors.

5. **Target family filtering** in `src/compiler/99.loader/module_resolver/resolution.spl`: `allowed_families` restricts stdlib family search for target presets.

**Remaining gap**: the manifest-backed hard violation API, Rust lint parity, Rust `simple check` strict mode, and Rust interpreter strict mode exist. Target preset entrypoints still need to thread strict runtime-family mode automatically instead of relying on explicit checker flags or `SIMPLE_STRICT_RUNTIME_FAMILY=1`. Default unrestricted CLI/interpreter runs intentionally keep compatibility warning output.

### Interpreter parity detail

- The interpreter module loader in `src/compiler/10.frontend/core/interpreter/module_loader.spl` has a **hardcoded search order**: `nogc_async_mut` > `nogc_async_immut` > `nogc_sync_immut` > `nogc_sync_mut` > `common` > `gc_async_mut` > `gc_async_immut` > `gc_sync_mut` > `gc_sync_immut` > `nogc_async_mut_noalloc`.
- `check_gc_family_boundary` emits interpreter warnings for no-GC→GC, noalloc→allocating-family, and higher-layer runtime-family imports.
- The Rust interpreter module loader uses the same family set, ranks, and reason strings as Rust `simple check`, and `SIMPLE_STRICT_RUNTIME_FAMILY=1` promotes loader family-boundary diagnostics to `[gc-error]` runtime errors.
- `test/unit/compiler/interpreter/gc_parity_spec.spl` covers family extraction and warning rules.

---

## Section 4: Known Gaps

### Native MCP/LSP smoke status (updated 2026-05-14)

- `src/app/mcp/main.spl` native-build now completes with the rebuilt Rust bootstrap compiler:
  - command: `src/compiler_rust/target/bootstrap/simple native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_mcp_server`
  - result: `Build complete: 122 compiled, 0 cached, 0 failed`; linked `build/bootstrap/mcp-package/simple_mcp_server`.
  - remaining caveat: unresolved native/runtime symbols still generate link stubs. Latest uncached run generated 714 unresolved-symbol stubs and no internal Simple stub warning.
- `src/app/simple_lsp_mcp/main.spl` native-build now completes with the rebuilt Rust bootstrap compiler:
  - command: `src/compiler_rust/target/bootstrap/simple native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_lsp_mcp_server`
  - result: `Build complete: 369 compiled, 0 cached, 0 failed`; linked `build/bootstrap/mcp-package/simple_lsp_mcp_server`.
  - remaining caveat: unresolved native/runtime symbols still generate link stubs. Latest traced uncached run generated 145 unresolved-symbol stubs, including 28 internal Simple symbols.
  - async backend update: `nogc_async_mut/io/tcp.spl` and `nogc_async_mut/io/udp.spl` are ready-future facades over `nogc_sync_mut.io.tcp` and `nogc_sync_mut.io.udp`. `gc_async_mut/io/tcp.spl` and `gc_async_mut/io/udp.spl` export the no-GC sync/async backends instead of declaring duplicate TCP/UDP runtime hooks, and `gc_async_mut/net/udp.spl` plus `nogc_async_mut/net/udp.spl` route through the no-GC sync UDP facade. The latest traced LSP build generated no `rt_io_tcp_*`, `rt_async_tcp_*`, `rt_async_udp_*`, or `rt_socket_set_nonblocking` stubs; remaining UDP hook mentions are sync no-GC backend hooks (`rt_io_udp_bind`, `rt_io_udp_local_addr`, `rt_io_udp_set_broadcast`, `rt_io_udp_set_read_timeout`).
  - facade closure update: Redis clients, `io/file_ops`, GC async `io/file`, no-GC async TLS setup, WebSocket close, and HTTP worker socket setup now route through no-GC backend modules. `gc_async_mut` and `nogc_async_mut` utility modules for `io_runtime`, `log`, `mcdc`, `process_ops`, `env_ops`, `time_ops`, `dir_ops`, `debug_state`, `file_discovery`, `file_shell`, `pipe`, `process_limit_enforcer`, `sysinfo_ops`, `thread`, `hooks/*`, selected `lsp/*`, `mem_tracker`, `qemu/qmp_client`, package distribution, package FFI, platform roots/linker, SIMD roots/profile helpers, security audit helpers, spec decorators, experiment storage/config/artifact/sweep helpers, play automation, and simple I/O helpers (`coverage_simple`, `math`, `profiler_simple`, `signal_stubs`, `volatile_ops`) are compatibility facades over `nogc_sync_mut`; no-GC async `debug_stubs`, `ssh_serial`, `cache/*`, `daemon_sdk/*`, `database/atomic`, `database/core`, `database/requirement`, `benchmark/string_bench`, `shell/env`, `spec/env_detect`, debug backends, environment types, OIDC helpers, desktop display, FFI helpers, GPU driver/runtime, media/device I/O FFI boundaries, WASI LSP main, JS interpreter glue, database helpers, desktop helpers, render/debug adapters, same-path coverage/atomic/config/fuzz helpers, MCP file/resource helpers, MCP entrypoint file/env/process/time/GC helpers, MCP protocol text-length helpers, MCP handler CLI argument helpers, async byte file helpers, SVLLM std-fs byte file/publish helpers, process-set config/manager/file-queue/identity helpers, async future timing and pure async SFFI helpers, web-framework file reads, LLM CLI/config/local-torch/provider file/env/process/time/HTTP helpers, DNS resolver file/time/text-byte helpers, HTTP static/worker file helpers, HTTP time helpers, access logging, HTTP compression text conversion, LLM diagnostics file/dir/env/time/stdin helpers, GPU shader-cache file persistence, linalg backend environment selection and staging-buffer raw pointer helpers, TLS I/O byte-wire/hex helpers, and reviewed import-drift FFI helpers also route to the no-GC sync backend or pure Simple helpers. No-GC async top-level atomic, cache operation/helper, DMA, volatile ops, top-level SIMD, SQLite FFI, database atomic/core/checker/requirement/todo, and desktop dialog/display/global_shortcut/lifecycle/notification/power/protocol/shell_open/tray/updater facades now use explicit public export lists over their no-GC sync owners so compatibility modules do not wildcard-export backend runtime hooks. GC async buffered I/O, torch FFI, CUDA GPU FFI, Vulkan compute/graphics FFI, OpenGL/Metal/ROCm/oneAPI I/O FFI, 2D/3D GPU FFI dispatch, 2D/3D CUDA/Vulkan/ROCm/Intel FFI wrappers, shared 2D/3D SIMD/color/type helpers, and the SVLLM NVFS std-fs adapter now route to no-GC async or no-GC sync backends to preserve API shape without duplicate runtime-hook ownership; no-GC async Torch FFI itself delegates to the no-GC sync Torch FFI because the runtime boundary is synchronous backend ownership. CUDA FFI hooks are now owned by the no-GC sync CUDA FFI/backend stack; no-GC async CUDA FFI is a facade, GC async GPU FFI is a facade, `gc_async_mut/gpu.spl` no longer contains comment-only `extern fn rt_cuda_*` scan noise, GC async Vulkan/OpenGL/Metal/ROCm/oneAPI FFI modules are facades over `nogc_sync_mut.io` owners, GC async GPU FFI dispatch/vendor wrapper/helper modules are facades over `nogc_sync_mut.gpu` owners, and async CUDA/GPU memory route raw pointer helpers through `nogc_sync_mut.ptr.raw`. Buffered I/O, sync file I/O, HTTP response text conversion, HTTP compression text conversion, and MCP protocol content-length conversion are pure in the relevant no-GC backends, with no local `rt_text_to_bytes`, `rt_bytes_to_text`, or `rt_text_byte_len` hooks; no-GC async file metadata now reuses no-GC sync file-ops wrappers for existence and size, no-GC async byte file futures and SVLLM std-fs byte writes/publish rename reuse `nogc_sync_mut.ffi.io`, LLM HTTP providers use `nogc_sync_mut.io.http_ffi.http_request_raw`, LLM diagnostics hook stdin uses `nogc_sync_mut.io.pipe.Stdin`, LLM diagnostics WebSocket export uses `nogc_sync_mut.io.http_ffi.ws_send_handle`, the top-level no-GC async concurrency aggregate reuses no-GC async channel/thread modules and no-GC sync atomic wrappers, no-GC async channel/thread/mutex/RwLock are facades over no-GC sync concurrency backends, async SFFI remains pure Simple with no local runtime-hook examples, TLS I/O nonce/AAD and hex helpers use `tls_common.encode_u8`, TLS stream hex crypto calls use TLS common hex-domain wrappers, and TLS handshake crypto calls use TLS common RSA/AES wrappers, directory entry hooks are owned by `nogc_sync_mut.io.dir_entry_ops`, mimalloc TLS adapters import thread-local runtime hooks from `nogc_sync_mut.runtime.thread_local` while keeping family-local heap types, browser session file reads and LLM diagnostics file exporters/parsers use `nogc_sync_mut.io.file_ops`, web-framework file reads and DNS resolver config reads use `nogc_sync_mut.io.file_ops.file_read_text`, DNS resolver TTL checks use `nogc_sync_mut.io.time_ops.current_time_unix`, DNS packet text conversion uses `text.bytes()` and `text.from_bytes`, async future timing uses `nogc_sync_mut.io.time_ops.current_time_ms`, HTTP server/health/worker/CSRF/rate-limit and LLM diagnostics timing helpers use `nogc_sync_mut.io.time_ops.current_time_ms`, HTTP access logging uses `nogc_sync_mut.io.file_ops.file_append`, LLM diagnostics environment scanning uses no-GC sync file, directory, and environment wrappers, MCP entrypoint/perf helpers use no-GC sync file, environment, process, time, and runtime GC wrappers, MCP subprocess handlers use `std.ffi.cli.cli_get_args`, process-set config/manager/IPC helpers use no-GC sync file, process, time, and process identity wrappers, and LLM CLI/config/local-torch/provider helpers use no-GC sync environment, process, file, and time wrappers while preserving HTTP backend ownership in provider modules. A source scan over `src/lib/gc_async_mut` and `src/lib/nogc_async_mut` finds no byte-identical runtime-hook copies of `nogc_sync_mut` backend files; no `rt_io_tcp_*`, `rt_async_tcp_*`, `rt_io_udp_*`, `rt_async_udp_*`, `rt_socket_set_nonblocking`, `rt_socket_set_reuse*`, `rt_epoll_*`, `rt_driver_*`, `rt_file_fsync*`, `rt_file_stat`, `rt_file_read_text` browser-session declarations, duplicated `rt_thread_local_*` references, or HTTP `rt_time_now_unix_micros` references remain in those compatibility-family HTTP time helpers. The raw socket hooks are concentrated in `nogc_sync_mut.io.tcp`. The reviewed no-GC async files with sync counterparts (`torch/ffi`, `cuda/ffi`, `cuda/mod`, `gpu/memory`, `http_server/response`, `io/buffer`, `io/file`, `package_ffi`, `platform`, `simd`, `mimalloc_tls`, `coverage`, `atomic`, `conf`, `fuzz`) now contain no local runtime-hook declarations; tracked no-GC async hook files now have no same-path no-GC sync counterpart.
  - Final no-GC async runtime-owner wildcard closure: historical step-down scans are superseded by the current static audit. The runtime-hook owner wildcard scan now reports `remaining=0`; new wildcard facades over runtime-hook owners require explicit architecture review.
  - GPU math hook update: GC async 3D backends now route shared `rt_f64_sqrt`, `rt_f64_sin`, and `rt_f64_cos` use through `nogc_sync_mut.gpu.engine3d.math_hooks`, so backend-local math hook ownership is not duplicated across the GC compatibility family.
  - GPU presentation hook update: GC async 2D and 3D CPU backends now route `rt_cpu_present_pixels` through `nogc_sync_mut.gpu.present_hooks`, keeping presentation runtime ownership in the no-GC backend while preserving backend method behavior.
  - Vulkan helper update: GC async 2D Vulkan helper dispatch now imports free wrappers from `nogc_sync_mut.gpu.engine2d.ffi_vulkan` instead of redeclaring helper-local `rt_vulkan_*` hooks.
  - Vulkan backend update: GC async 2D Vulkan backend initialization, shader, pipeline, buffer, and readback calls now import free wrappers from `nogc_sync_mut.gpu.engine2d.ffi_vulkan` instead of declaring backend-local `rt_vulkan_*` hooks.
  - Metal helper update: GC async 2D Metal helper dispatch now imports command, encoder, and buffer wrappers from `nogc_sync_mut.io.metal_ffi` instead of redeclaring helper-local `rt_metal_*` hooks.
  - Metal backend update: GC async 2D Metal backend initialization, shader, pipeline, buffer, and queue calls now import raw-handle wrappers from `nogc_sync_mut.io.metal_ffi` instead of declaring backend-local `rt_metal_*` hooks.
  - WebGPU backend update: GC async 2D WebGPU backend runtime calls now import wrappers from `nogc_sync_mut.gpu.engine2d.webgpu_ffi` instead of declaring backend-local `rt_webgpu_*` hooks.
  - Runtime facade execution update: GC async TLS, TCP, WebSocket, web-framework, hooks/detectors, HTTP/3, MCP SDK server/transport, play/CDP, sanitizer, security, storage, replay, `src` compatibility, terminal, web UI, TUI, STOMP, text layout, UI test, SPostgre IF, unsafe, test, testing, UI, tmux, test-runner, timing, UDP utility, and DB acceleration/DBFS driver/DBFS engine facade modules now route to `nogc_async_mut` backends instead of self-re-exporting or remaining missing GC-local package surfaces. The tracked one-line `gc_async_mut` self-facade scan, including top-level `gc_async_mut/*.spl`, now reports zero remaining files. The no-GC sync MCP SDK JSON owner now provides a local `escape_json` helper so imported symbols are not re-exported through facade chains; the no-GC sync replay checkpoint owner now provides local printable-ASCII decode support so replay facade chains do not depend on an imported text helper at runtime. No-GC sync sdoctest parsing now uses built-in text splitting/trimming instead of an unresolved `common.text` import, no-GC sync DBFS driver text operations use built-in text slices instead of unresolved `common.string_core.str_char_at`, no-GC TLS hex helpers avoid interpreter-only slice lowering, no-GC sync CUDA FFI normalizes runtime status codes into the public boolean/handle contract, and the GC async 2D WebGPU fallback text path no longer depends on optional dynamic font-renderer construction.
  - GC async runtime-owner wildcard update: GC async runtime-hook-owner facades now route through no-GC async facades where matching no-GC async surfaces exist. The remaining GPU 2D/3D and device I/O FFI API-shape gaps now have no-GC async facades over explicit no-GC sync backend export lists, and the GC async facades export those no-GC async surfaces instead of wildcard-exporting no-GC sync runtime-hook owners directly. `scripts/audit/runtime_backend_boundaries.py` now reports `gc_async_runtime_owner_wildcard_facade_count=0`.
  - Framebuffer hook update: GC async VirtIO-GPU presentation now imports `rt_fb_blit32` through `nogc_sync_mut.gpu.engine2d.framebuffer_hooks` instead of declaring the blit hook locally.
  - Engine helper hook update: GC async CUDA, ROCm, and Intel 2D engine backends now import argument-packing, pixel-transfer, and kernel-argument helpers from the no-GC sync engine FFI owners instead of declaring those runtime hooks locally.
  - CUDA I/O facade update: GC async `io/cuda_ffi.spl` now re-exports the legacy Simple-friendly CUDA I/O ABI from `nogc_sync_mut.io.cuda_ffi`, leaving no tracked `gc_async_mut` runtime-hook declarations.
  - No-GC async hook-owner update: actor runtime calls, TLS common crypto/wire helpers, and raw async WebSocket frame I/O now import no-GC sync hook owners, leaving no tracked `nogc_async_mut` runtime-hook declarations.
  - simple-core async ABI update: `src/runtime/simple_core/core_async.spl` now defines the `rt_future_*` and compiler-lowered `rt_async_*` state-machine symbols in pure Simple. `std.async.Future<T>` now stores `Poll<T>` directly instead of using the old `future_alloc_*` opaque-state FFI. A traced LSP build with `SIMPLE_NATIVE_RUNTIME_BUNDLE=rust-hosted SIMPLE_RUNTIME_PATH=src/compiler_rust/target/bootstrap` generated 494 stubs and no `rt_async_*`, `rt_future_*`, `future_*`, `promise_*`, or `async_*` runtime ABI stubs.
  - simple-core atomic ABI update: `src/runtime/simple_core/core_atomic.spl` now defines the raw-pointer `rt_atomic_*` fallback symbols used by `std.log`. The fallback is no-GC and platform-neutral but only preserves single-thread/bootstrap semantics; true concurrent atomics remain a hosted/platform responsibility. `std.log` now routes its bootstrap ring through local raw-pointer helpers, and the traced LSP build generated 489 stubs with no `rt_atomic_*` runtime ABI stubs.
  - native warning closure update: HIR import loading now treats empty grouped/glob root imports as non-addressable facade roots instead of resolving an empty module path. The core C runtime now exports handle-based `rt_atomic_int_*` and `rt_atomic_bool_*` atomics plus minimal enum/BDD helper ABI used by focused native BDD smoke. A rebuilt `src/compiler_rust/target/debug/simple` native run of `test/unit/lib/{gc_async_immut,gc_sync_immut,nogc_sync_immut}/trie_root_facade_native_spec.spl` passed all three focused specs with no empty-module type-loader warnings, no internal Simple symbol warnings, and no generated runtime stubs.
  - time ABI update: `src/lib` call sites now use the canonical `rt_time_now_unix_micros` ABI and derive millisecond/nanosecond views locally. This removed the `rt_time_now_ms` and `rt_time_now_ns` package stubs; the traced LSP build generated 487 stubs and the remaining time stubs are compiler/tooling declarations (`rt_time_now_micros`, `rt_time_now_nanos`, `rt_time_now_unix`).
  - driver source update: `std.io.driver.IoDriver` now defaults to a pure Simple no-GC fallback (`simple-fallback`) that supports timeout completion smoke behavior and reports kernel I/O as unsupported (`-38`) until a platform driver is selected. No `src/lib` source file imports `rt_driver_*` after this change.
  - native retention update: native runtime retention now roots object undefineds plus explicit codegen roots instead of keeping every declared runtime import reachable. The latest traced LSP build generated no `rt_driver_*`, `rt_file_fsync*`, or `rt_epoll_*` stubs.
  - event/file fallback update: default `nogc_async_mut` event-loop registration now uses a cooperative Simple-level readiness fallback instead of importing `rt_epoll_*`; async/sync file operation facades no longer import `rt_file_fsync*`, and async file metadata no longer imports handle-based `rt_file_stat_*`. The portable fallback reports successful fsync only when the path exists and derives file metadata from path-based file ABI plus directory-open probing. Platform backends can still provide stronger POSIX durability/readiness semantics behind a selected backend.
  - SimpleOS POSIX boundary update: shared ABI errno values, FD table/I/O, async read/write adapters, pipe/socket compatibility, and process async/compatibility wrappers are now owned under `src/os/kernel/`. The matching `src/os/posix/` modules are POSIX compatibility facades. Hosted NVFS root access now imports `std.fs_driver.nvfs_hosted_driver.NvfsHostedDriver`, a neutral facade over the existing POSIX-compatible hosted adapter, so SimpleOS boot/VFS layers do not import the POSIX-named stdlib driver directly. A targeted scan finds no `os.posix` imports or POSIX-named NVFS driver imports under `src/os/kernel`, `src/os/services`, or `src/os/sosix`; those lower layers now depend on `os.kernel` and hosted-neutral ownership instead.
  - implication: MCP and LSP native smoke are no longer blocked by `SliceIter.slice`, enum/static-member resolution, shell status wrappers, stale `MirBlock.has_label` reads, or the last C/LLVM/native/Vulkan field-recovery failures. Package release-readiness still requires reducing native/runtime stubs and broader import/type-loading cleanup.

### Gap 1: Target-restricted family hard errors are partially wired (Agent 2 -- Compiler)
- **Problem**: Public runtime-family root `__init__.spl` files carry `@no_gc` or `@gc`, the Simple semantic checker exposes manifest-backed hard violations, and the Rust `simple check` lint path mirrors the manifest family set/ranks/reason strings. The Rust check path now promotes those diagnostics to errors when invoked with `--deny-gc-boundary` / `--strict-runtime-family`, while unrestricted checks keep warnings.
- **Impact**: Target-restricted checker/CI runs can fail on runtime-family boundary violations; compiler pipelines that do not pass a strict target-family option still remain warning-compatible.
- **Fix**: Thread target presets into every compiler entrypoint that needs strict family enforcement instead of relying on callers to pass the explicit checker flag.

### Gap 2: Interpreter strict family errors require explicit opt-in (Agent 3 -- Interpreter)
- **Problem**: The Rust interpreter can now promote family-boundary diagnostics to errors with `SIMPLE_STRICT_RUNTIME_FAMILY=1`, but target presets do not yet set that mode automatically.
- **Impact**: Target-restricted interpreter gates can fail on runtime-family boundary violations when strict mode is enabled; unrestricted interpreter runs still intentionally continue after warning.
- **Fix**: Thread target presets into interpreter launch/configuration so baremetal/noalloc and other restricted target runs enable strict runtime-family mode without manual environment setup.

### Gap 3: `nogc_async_immut` runtime coverage (Agent 3/4) -- **RESOLVED**
- **Status**: Fixed. Persistent-structure facade coverage is broad, and `test/unit/lib/nogc_async_immut/coordination_native_spec.spl` now covers direct no-GC async `Atom`, `Ref`, `VersionedSnapshot`, and exported CAS helper behavior in interpreter and native modes.
- **Remaining work**: Keep this spec in native smoke; broader public promotion still depends on manifest-backed capability enforcement.

### Gap 4: `nogc_async_mut_noalloc` root `__init__.spl` (Agent 4 -- Stdlib) -- **RESOLVED**
- **Status**: Fixed. The root `__init__.spl` now declares `@no_gc`, sub-modules, and the baremetal/noalloc export surface.
- **Remaining work**: Direct imports from allocating runtime families, direct `app.*` imports, explicit noalloc `@alloc` markers, and host allocation API calls are blocked by `dependency_boundary_spec` and the baremetal verifier; deeper allocation capability enforcement is still partial.

### Gap 5: Compiler-owned allocation capability scanning is still partial (Agent 2 -- Compiler)
- **Problem**: target family filtering, direct-import tests, marker tests, reachable-import closure audit, the baremetal verifier, and the runtime-family manifest block or report noalloc imports from allocating runtime families, direct `app.*` imports, explicit noalloc `@alloc` opt-ins, direct host allocation APIs, and unsafe reachable helper imports. Reachable closure enforcement is still partly script/verifier-owned rather than fully compiler-owned.
- **Impact**: Baremetal builds are protected against direct and reachable family-boundary mistakes, and the noalloc family is checker-clean under rebuilt `simple check`, but deeper reachable allocation safety is not yet represented as first-class module metadata throughout compiler/module resolution.
- **Fix**: Feed the runtime-family manifest into compiler/module resolution for target-restricted runs and retain the reachable-import audit as regression evidence until the compiler owns the full closure.

### Gap 6: `gc_sync_mut` had tests but no source (Agent 4 -- Stdlib) -- **RESOLVED**
- **Status**: Fixed. `src/lib/gc_sync_mut/` now exists as a facade-only compatibility family over tracked `gc_async_mut` modules.
- **Decision**: `gc_sync_mut` is advanced-scoped, not an independent backend owner. Runtime hooks and behavior stay in the existing async/no-GC-backed implementation chain.
- **Remaining work**: Focused import and interpreter behavior tests exist; decide whether any API requires real blocking wrappers instead of facade exports.

### Gap 7: Two conflicting `GcMode` enums (Agent 2 -- Compiler) -- **RESOLVED**
- **Status**: Fixed. `gc_config.spl` owns the only `GcMode {Gc, NoGc}` enum, and `barriers.spl` uses `GcStrategy {StopTheWorld, Incremental, Generational, Concurrent}` for GC algorithm strategy.
- **Guard**: `test/unit/compiler/semantics/gc_strategy_naming_spec.spl` prevents a second compiler `enum GcMode:` from being introduced.

### Gap 8: No target preset maps to family (Agent 5 -- Target Presets) -- **RESOLVED**
- **Problem**: Target presets described no-GC/no-std targets but did not carry runtime-family restrictions into compile options.
- **Impact**: A baremetal build could import from any family directory.
- **Fix**: Presets now expose `allowed_families`; `preset_apply_compile_options()` copies `no_gc` and `allowed_families` into `CompileOptions`.
- **Resolution**: `src/compiler/70.backend/target_presets.spl` carries runtime-family restrictions, `src/compiler/00.common/driver_core_types.spl` stores them on `CompileOptions`, and `src/compiler/99.loader/module_resolver/resolution.spl` filters `lib/*/` search when restrictions are non-empty. Covered by `test/unit/compiler/driver/compile_options_normalization_spec.spl`, `test/unit/compiler/target_presets_spec.spl`, and `test/unit/compiler/module_resolver/allowed_families_spec.spl`.

### Gap 9: `nogc_async_immut` root exports (Agent 4 -- Stdlib) -- **RESOLVED**
- **Status**: Fixed. The root `__init__.spl` now declares `@no_gc`, sub-modules, and exports the persistent collections, `Atom`, `Ref`, `VersionedSnapshot`, and combinators.
- **Evidence**: Direct coordination/CAS native coverage now passes through `test/unit/lib/nogc_async_immut/coordination_native_spec.spl`.

### Gap 10: Interpreter GC boundary execution coverage (Agent 6 -- Tests) -- **RESOLVED**
- **Status**: Fixed. `test/unit/compiler/semantics/gc_boundary_check_spec.spl` directly covers the production `check_gc_boundary_imports()` rules, `src/app/cli/query_lint.spl` surfaces those warnings through query diagnostics, `simple check` emits `gc_boundary_crossing` warnings through the Rust driver check path with manifest-equivalent reason strings, and the Rust interpreter module loader now emits `[gc-warning]` for real no-GC->GC, noalloc->allocating, and higher-layer runtime-family import paths, including `src/std/<family>` imports. With `SIMPLE_STRICT_RUNTIME_FAMILY=1`, the Rust interpreter promotes the same loader diagnostics to `[gc-error]` runtime errors.
- **Evidence**: A rebuilt bootstrap `simple run` on a no-GC file importing `std.gc_async_mut.{gpu_device_count}` emits one no-GC context warning before normal execution.
- **Remaining work**: Thread target presets into interpreter launch/configuration so restricted targets enable strict runtime-family errors automatically.

---

## Section 5: Early Decisions

### Decision 1: Which runtime families are truly public?

**Answer**: Five families are public based on code evidence:

| Family | Evidence |
|--------|---------|
| `common` | 1166 files, in interpreter search path, rich exports |
| `nogc_sync_mut` | 1434 files, in interpreter search path, primary systems family |
| `nogc_async_mut` | 1688 files, default interpreter search priority, actor/async system |
| `gc_async_mut` | 914 files, in interpreter search path, GC-capable async family with GPU/ML-specific extras |
| `nogc_async_mut_noalloc` | 128 files, in interpreter search path, baremetal with QEMU tests |

Five families are **advanced-scoped** (exist but still have promotion gaps): `nogc_async_immut`, `gc_sync_mut`, `gc_async_immut`, `gc_sync_immut`, and `nogc_sync_immut`. The sync/GC and sync/immutable variants are facade-only compatibility surfaces backed by existing async/no-GC families.

### Decision 2: Is interpreter parity mandatory for all public families?

**Answer**: Yes for the 5 public families, with caveats:
- The interpreter currently achieves module-resolution parity via the hardcoded search order.
- The interpreter emits family-boundary warnings for no-GC→GC, noalloc→allocating-family, and higher-layer runtime-family imports.
- `SIMPLE_STRICT_RUNTIME_FAMILY=1` promotes those interpreter diagnostics to errors for target-restricted gates.
- **Minimum bar**: Interpreter must resolve modules from all 5 public families and emit warnings on cross-family GcMode mismatches (currently true).
- **Stretch goal**: target-preset-restricted interpreter runs should enable strict runtime-family errors automatically.
- `nogc_async_immut` is already in the search order; the remaining promotion gates are broader compiled/runtime coverage.

### Decision 3: Which stdlib differences are intentional vs accidental?

**Intentional differences** (by design):
- `common` has no `me` methods (stateless utility library).
- `nogc_async_immut` data structures return new versions instead of mutating (persistent data design).
- `nogc_async_mut_noalloc` forbids heap allocation (baremetal constraint).
- `gc_async_mut` requires GC runtime (GPU memory management model).

**Accidental differences** (bugs to fix):
- Interpreter GcMode enforcement is still missing for `nogc_async_immut` and the other public families.
- `gc_sync_mut`, `gc_async_immut`, `gc_sync_immut`, and `nogc_sync_immut` are facade-only and still need focused resolution/runtime coverage.
- Duplicate module exports across families (e.g., `io_runtime`, `platform`, `spec`, `log` appear in both `nogc_sync_mut` and root `lib/__init__.spl`).

### Decision 4: Which target presets are authoritative for no-GC?

**Answer**: The implemented target presets live in `src/compiler/70.backend/target_presets.spl`:

| Preset | Triple | Heap | Allowed Families |
|--------|--------|------|------------------|
| `cortex-m4` | `thumbv7em-none-eabihf` | none | `nogc_async_mut_noalloc`, `common` |
| `cortex-m0` | `thumbv6m-none-eabi` | none | `nogc_async_mut_noalloc`, `common` |
| `riscv32-baremetal` | `riscv32imac-none-ilp32` | none | `nogc_async_mut_noalloc`, `common` |
| `avr-atmega328` | `avr-none-avr` | none | `nogc_async_mut_noalloc`, `common` |
| `i8086-dos` | `i8086-dos-cdecl` | none | `nogc_async_mut_noalloc`, `common` |
| `i8086-baremetal` | `i8086-none-cdecl` | none | `nogc_async_mut_noalloc`, `common` |
| `wasm32` | `wasm32-wasi-wasm` | fixed heap | `nogc_async_mut_noalloc`, `nogc_sync_mut`, `nogc_async_mut`, `common` |
| hosted presets | Linux/macOS/Windows/RISC-V Linux | platform heap | unrestricted |

The `gc_off` flag in `CompileOptions` remains a global no-GC switch; `allowed_families` is the target-family restriction used by module resolution.

**Resolved**: Target presets now explicitly set family restrictions via `TargetPreset.allowed_families`, `preset_allowed_families()`, and `preset_apply_compile_options()`. See Section 6.

### Decision 5: What counts as "complete" for weakest families?

**For `nogc_async_immut`** (advanced-scoped, weakest existing):
- [x] Add to interpreter module loader search order
- [x] Export core types from `__init__.spl`
- [x] Add `@no_gc` attribute to `__init__.spl`
- [x] Add broad native persistent-structure facade coverage
- [x] Verify CAS atom operations work in compiled mode

**For `gc_sync_mut`** (advanced-scoped facade):
- [x] Add `src/lib/gc_sync_mut/` facade tree backed by `gc_async_mut`
- [x] Add `@gc` root
- [x] Add interpreter fallback search and family extraction
- [x] Add focused import and interpreter behavior tests
- [ ] Decide whether selected APIs need true blocking wrappers

**For `gc_async_immut`, `gc_sync_immut`, and `nogc_sync_immut`** (advanced-scoped facades):
- [x] Add facade trees backed by `nogc_async_immut` / `gc_async_immut`
- [x] Add root GC/no-GC attributes
- [x] Add interpreter fallback search and family extraction
- [x] Add focused import and interpreter behavior tests
- [x] Add native pure-combinator facade coverage
- [x] Run the broad 31-spec native immutable facade batch without warning/stub output
- [x] Fix native Atom/VersionedSnapshot runtime behavior across the facade families
- [x] Add focused native root `PersistentList` facade coverage
- [x] Add partial native root `PersistentVec` empty/repeated-push/tail-set/from_array smoke coverage across GC async, GC sync immutable, and no-GC sync immutable facades
- [x] Fix committed-path native `PersistentMap`/`PersistentSet` facade probe blocker with root `PersistentMap` set/get/overwrite/removal and `PersistentSet` add/contains/dedupe/removal one-entry, two-entry, and branch-shaped smoke across GC async, GC sync immutable, and no-GC sync immutable facades
- [x] Resolve native BDD blocker for untyped chained root-facade trie mutation
- [x] Clear focused immutable native type-loader/minimal-runtime-stub warnings

---

## Section 6: Target Preset to Runtime Family Mapping

> Added 2026-04-04 by Agent 5 (Target Presets & Baremetal Mapping).

### 6.1 Preset Definitions

Target presets are defined in `src/compiler/70.backend/target_presets.spl` as `TargetPreset` values.
Each preset specifies:
- `allowed_families`: Which runtime families the module resolver may search
- `gc_off`: Whether GC is disabled
- `heap_size`: Whether the preset has no heap (`0`) or a fixed/platform heap

### 6.2 Preset-to-Family Mapping Table

| Preset class | `gc_off` | Heap | Allowed Families | Use Case |
|--------------|----------|------|-----------------|----------|
| baremetal MCU/retro | true | none | `nogc_async_mut_noalloc`, `common` | bare-metal, BIOS/DOS-like, QEMU |
| `wasm32` | true | fixed | `nogc_async_mut_noalloc`, `nogc_sync_mut`, `nogc_async_mut`, `common` | no-GC embedded/portable heap |
| hosted | false | platform | *(all families)* | desktop/server |

### 6.3 Fallback Chain per Preset

**Baremetal** (most restrictive):
```
nogc_async_mut_noalloc → common → (reject)
```

**EmbeddedWithHeap**:
```
nogc_async_mut_noalloc → nogc_sync_mut → nogc_async_mut → common → (reject)
```

**Hosted** (no restriction, uses default search order):
```
nogc_async_mut → nogc_async_immut → nogc_sync_immut → nogc_sync_mut → common → gc_async_mut → gc_async_immut → gc_sync_mut → gc_sync_immut → nogc_async_mut_noalloc
```

### 6.4 How Family Restriction Works

1. `preset_apply_compile_options()` returns a `CompileOptions` with `gc_off` and `allowed_families` copied from the selected `TargetPreset`.
2. The caller passes `CompileOptions.allowed_families` to `ModuleResolver.with_allowed_families()`.
3. In `resolution.spl`, the lib subdirectory search loop (`lib/*/`) skips any subdirectory not in `allowed_families` (when the list is non-empty).
4. Empty `allowed_families` means no restriction (backward-compatible default).

### 6.5 How to Override the Default Family

To restrict families manually (without a preset):
```simple
var opts = CompileOptions.default()
opts.allowed_families = ["nogc_sync_mut", "common"]
```

To create a resolver with family restriction:
```simple
val resolver = ModuleResolver.new(project_root, source_root)
    .with_allowed_families(["nogc_async_mut_noalloc", "common"])
```

### 6.6 Implementation Files

| File | Change |
|------|--------|
| `src/compiler/00.common/driver_core_types.spl` | Added `allowed_families: [text]` to `CompileOptions`, `is_family_allowed()` method |
| `src/compiler/70.backend/target_presets.spl` | `TargetPreset.allowed_families`, `preset_allowed_families()`, `preset_apply_compile_options()` |
| `src/compiler/99.loader/module_resolver/types.spl` | Added `allowed_families: [text]` to `ModuleResolver`, `with_allowed_families()` |
| `src/compiler/99.loader/module_resolver/resolution.spl` | Added family filtering in lib subdirectory search loop |
| `test/unit/compiler/target_presets_spec.spl` | Added family mapping tests |
| `test/unit/compiler/driver/compile_options_normalization_spec.spl` | Verifies presets apply `gc_off` and `allowed_families` to `CompileOptions` |
| `test/unit/compiler/module_resolver/allowed_families_spec.spl` | Verifies resolver source keeps the `allowed_families` filter path |

---

## Appendix A: File Inventory by Family

| Family | `.spl` Files | Sub-modules | `__init__.spl` Exports |
|--------|-------------|-------------|----------------------|
| `common` | 1166 | iterator/, text/, math/, encoding/, crypto/, json/, sdn/, regex/, color/, date/, uuid/, ... | Via parent `src/lib/__init__.spl` |
| `nogc_sync_mut` | 1434 | io/, fs/, net/, ffi/, db/, debug/, allocator/, gc, simd/, tui/, spec/, engine/, editor/, database/, ... | Rich canonical sync systems surface |
| `nogc_async_mut` | 1688 | actor/, async, concurrent, gen_server, supervisor, mailbox, thread_pool, coroutine, generator, engine/, editor/, database/, ... | Rich async/no-GC surface with complete canonical sync parity plus async-specific extras |
| `gc_async_mut` | 914 | gpu, cuda/, torch/, gpu_runtime/, engine/, editor/, database/, io/, net/, http/, ... | GC async surface with complete canonical sync parity plus GC/GPU-specific extras |
| `nogc_async_immut` | 22 | persistent data structures, Atom/Ref, versioned snapshots, combinators | Root exports persistent structures, coordination types, combinators, and version |
| `nogc_async_mut_noalloc` | 128 | baremetal/ (6 archs), execution/, memory/, async/, collections/, qemu/, io/, log/, math/, string/, hash/, sort/ | Root exports baremetal/noalloc modules and version |

## Appendix B: Compiler GC Infrastructure Map

| File | Layer | Purpose | Connected to Families? |
|------|-------|---------|----------------------|
| `src/compiler/00.common/gc_config.spl` | L00 | `GcMode {Gc, NoGc}`, `GcConfig`, provenance tracking | No (attribute-based, not directory-based) |
| `src/compiler/00.common/gc_boundary.spl` | L00 | `GcBoundaryChecker`, cross-mode call/return/conversion warnings | No (checks attribute GcMode, not family) |
| `src/compiler/99.loader/module_resolver/manifest.spl` | L99 | Parses `@no_gc`/`@gc` from `__init__.spl` attributes, propagates to `ChildModule.gc_config` | **Partial**: runtime-family roots now use attributes, but manifest-to-hard-error enforcement remains partial |
| `src/compiler/55.borrow/gc_analysis/barriers.spl` | L55 | Write barrier analysis (`GcStrategy {StopTheWorld, Incremental, Generational, Concurrent}`) | No (MIR-level analysis, separate GC strategy enum) |
| `src/compiler/55.borrow/gc_analysis/mod.spl` | L55 | `GcSafetyAnalyzer`, root tracking, escape analysis | No (operates on MIR, not module families) |
| `test/unit/lib/dependency_boundary_spec.spl` | Test | Blocks direct noalloc imports from allocating runtime families, direct `app.*` imports, noalloc `@alloc` markers, host allocation APIs, and unsafe reachable helper imports | Yes for direct imports/markers/API calls/reachable helper imports; compiler-owned capability metadata remains future work |
| `src/compiler/90.tools/verify/baremetal.spl` | L90 | Baremetal verification surface | Enforces current direct and reachable noalloc source constraints; should consume future manifest-level allocation metadata |
| `src/compiler/00.common/driver_core_types.spl` | L00 | `CompileOptions.gc_off` flag | No (global toggle, not per-family) |
| `src/compiler/10.frontend/core/interpreter/module_loader.spl` | L10 | Hardcoded family search order for `use std.*` resolution | **Yes** (only place families are explicitly listed) |

## Appendix C: Test Coverage Map

| Test File | Tests Family | Type |
|-----------|-------------|------|
| `test/unit/compiler/common/gc_config_spec.spl` | GcMode/GcConfig types | Unit |
| `test/unit/compiler/semantics/gc_safety_spec.spl` | GC safety analysis | Unit |
| `test/feature/usage/gc_managed_default_spec.spl` | GC managed default behavior | Feature |
| `test/feature/lib/gc_parity/gc_module_loader_spec.spl` | GC module loader parity | Feature |
| `test/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl` | nogc_sync_mut sync GC-adjacent contracts | Feature |
| `test/system/features/gc_system_spec.spl` | GC system-level | System |
| `test/lib/std/unit/gc_spec.spl` | GC stdlib unit | Unit |
| `test/unit/lib/gc_async_mut/gpu_runtime/gc_borrowed_view_spec.spl` | GPU borrowed views | Unit |
| `test/unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.spl` | CUDA ownership | Unit |
| `test/unit/lib/gc_async_mut/torch/gc_*_spec.spl` (3 files) | Torch GC integration | Unit |
| `test/unit/lib/nogc_sync_mut/gc_runtime_contract_spec.spl` | NoGC sync GC metadata and pointer helper contracts | Unit |
| `test/unit/compiler/target_presets_spec.spl` | Target presets | Unit |
| `test/system/baremetal_test_runner_spec.spl` | Baremetal test runner | System |
