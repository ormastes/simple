# Key words and key points

## Crate
Package and module are used in many different meaning across different languages.
Crate is simple.sdn exist deployment package unit.

## Virtual Crate
In a crate, there are one or many virtual crates.
Virtual crate is a top most dir with __init__.spl. 
It is not crate but have own export rule and configs.

## Linker Wrapper
Linker wrapper is the native link entry point.

- Input can be `.o`, `.smf`, or `.lsm`.
- For native objects it calls platform linker directly (prefer `mold`, then `lld`, then `ld`/`cc` fallback).
- For `.smf`/`.lsm` it asks ObjectProvider for object bytes.
- If object bytes are missing, it falls back to exported code units and assembles temporary `.o` files through shared `object_emitter`.
- `--fixed-be` is the strict validation flag for this path. It aliases to the fixed LLVM backend preference and disables soft fallback for backend-mismatched SMF materialization.
- Then it links all resolved objects into final native binary (or self-contained fallback when needed).

## Smf Getter 
SmfGetter locates and reads requested SMF/LSM modules.

- Supports both direct `.smf` files and indexed `.lsm` libraries.
- Returns raw SMF bytes and, when present, embedded object bytes.
- ObjectProvider composes SmfGetter + ObjTaker and adds cache/shared policy:
- SMF byte cache
- object byte cache
- deferred/template symbol materialization through ObjTaker
- exported code-unit fallback for modules without embedded `.o`

## Smf Loader
Loader runtime path:

1. Resolve module through ObjectProvider.
2. Read exported symbols/code.
3. Allocate executable memory.
4. Copy code into memory, apply relocations, then apply RW->RX protection.
5. Register loaded symbols in global symbol table only after relocation succeeds.
6. JIT/ObjTaker path handles deferred/generic symbols on demand using the shared SMF cache and shared executable mapper.

PIC rule:
- Loader assumes PIC for direct code embedding path.
- Non-PIC modules are rejected for raw-code embedding path.

## Obj mapper (Loader + JIT shared)
Compact research result for sharing SMF loader mapper and JIT mapper.

Current state:
- Loader path already maps bytes with native mmap helpers (`native_alloc_exec_memory`, `native_write_exec_memory`, `native_make_executable`) and tracks symbols in loader table.
- JIT path still has local exec-memory stubs (`alloc_exec_memory`, `write_exec_memory`, `flush_icache`) and a separate `jit_cache` + `symbol_table`.
- This duplicates symbol/address ownership logic and can diverge on lifecycle rules.

Option A: one mapper + mode config
- One `ObjectMapper` type with `mode: Loader | Jit`.
- Pros: minimal type surface.
- Cons: quickly grows conditionals for very different lifecycles (module unload vs symbol replace/re-JIT).

Option B: shared mapper core + thin wrappers (recommended)
- Build one low-level shared core: `SharedExecMapper`.
- Build two policy wrappers:
  - `LoaderMapper` (module ownership, bulk unload by module path)
  - `JitMapper` (symbol ownership, replace-on-recompile, JIT cache binding)
- Pros: shared alloc/write/protect/free path and stats, but lifecycle policy stays clean.
- Cons: small wrapper layer to maintain.

Option C: keep separate mappers, share allocator only
- Lowest refactor risk.
- Still leaves duplicate symbol table + ownership code.

Recommended architecture (Option B):
- Shared core responsibilities:
  - Allocate RW memory, copy bytes, switch to RX, optional icache flush.
  - Track mapped records: `{owner_id, symbol, address, size, generation}`.
  - Support `lookup(symbol)`, `unmap_owner(owner_id)`, `replace(symbol)`, `stats()`.
- Loader wrapper config:
  - `owner_id = module_path`
  - disallow `replace(symbol)` unless hot-reload enabled
  - unload by module path on reload/unload
- JIT wrapper config:
  - `owner_id = "__jit__"` or per-template bucket
  - allow `replace(symbol)` for re-instantiation
  - bind to JIT metadata cache

Security/performance rules:
- Prefer W^X flow: RW allocate -> write -> RX protect (not long-lived RWX).
- Keep icache flush hook in shared core (no-op on x86_64, required on ARM/RISC-V).
- Page-align arena chunks and keep per-owner free lists to reduce mmap churn.

Implementation order:
1. Add `src/compiler_shared/loader/object_mapper.spl` as shared core + config structs.
2. Replace loader local helper (`moduleloader_allocate_exec`) to call shared mapper.
3. Replace JIT exec stubs to call shared mapper; keep JIT compile logic unchanged.
4. Add tests:
   - loader + JIT both map via shared mapper
   - module unload frees owner allocations
   - JIT replace updates symbol address safely

Current gaps found and better way:
- Keep shared core (`SharedExecMapper`) but split policy into two facades:
  - `LoaderMapper`: strict module ownership + unload cleanup
  - `JitMapper`: replace-friendly JIT policy + cache integration
- Avoid global JIT owner for module-linked instantiations:
  - Prefer `owner_id = smf_path` for JIT-compiled symbols originating from a module.
  - This lets module unload/hot-reload reclaim JIT mappings correctly.
- Unload should remove all global symbol-table entries by owner path, not only base exported symbols.
  - Generic/JIT-added symbols can otherwise leave stale entries after memory unmap.
- Keep one source of truth for executable mapping lifecycle:
  - no direct mmap/write/protect calls outside shared mapper
  - no per-component free logic outside mapper API

Decision:
- Best tradeoff is **shared core + Loader/JIT policy wrappers**.
- One mapper with only config flags is workable but tends to grow mode conditionals and weak ownership rules.

## Remote interpreter
Remote interpreter executes same frontend/lowering contract but targets remote memory.

- Generates JIT/native code units.
- Requests exec allocation from remote mapper.
- Uses memory copier bridge (gdb/trace32/etc.) to place bytes remotely.
- Keeps local/remote behavior identical except memory transport backend.

## Remote Smf Loader
Not fully enabled yet.
Design is the same as local loader + remote memory copier backend.

## Memory copyer
Memory copier abstracts byte transfer.

- Local: plain memcpy/no-op abstraction layer.
- Remote baremetal: host -> target transfer via debugger/transport.

## Switchable backend
Simple uses two codegen backends:

- LLVM: release/native-focused builds.
- Cranelift: fast debug/dev path.

## Graphics Session
A `GraphicsSession` is the persistent backend lifetime object for rendering and
GPU/CPU acceleration. It owns or references backend state such as a CPU raster
context, CUDA context/interop state, Vulkan device and queues, Metal device and
command queue, WebGPU device and queue, allocators, command pools, caches,
capability records, and performance counters.

The session model applies across:

- 2D engine
- 2D game engine
- 3D engine
- 3D game engine
- web renderer
- GUI library
- window manager

Public APIs should be Pure Simple first. Native GPU calls should cross a stable
C ABI shim where the platform API requires native binding. A Rust runtime library
must not be the required graphics backend boundary.

## Legacy No-Session Graphics Mode
`LegacyNoSession` preserves old constructors and smoke-test APIs that do not ask
the caller to pass a session. Implementations may create short-lived resources
internally, but must not silently join managed shared caches or perf-exclusive
benchmark state.

Use it for compatibility and one-shot tests. Do not use it as the preferred API
for multi-window apps, games, web rendering, or benchmarking.

## Managed Shared Graphics Mode
`ManagedShared` is the normal app/game/UI mode. A managed session may retain and
share expensive resources across frames and related surfaces: device handles,
queues, allocators, shader and pipeline caches, immutable capability records, and
optimization provider facts.

Managed state is valid only inside the same session generation and compatible
policy hash. Device loss, backend switch, policy change, or target-feature change
must invalidate affected handles and provider facts.

## Perf Exclusive Graphics Mode
`PerfExclusive` is the benchmark/profiler mode. It isolates queues, allocators,
command pools, mutable pipeline caches, warmup state, and timing counters from
managed sessions so measurements are not polluted by app-managed state.

Perf mode may read immutable capability tables, but must reject mutable resource
sharing with `ManagedShared`. Cross-mode sharing errors should be typed and
visible in tests.

## Graphics Optimization Provider
A graphics optimization provider is a Simple Optimization Plugin provider used
by rendering and backend code. It can persist facts such as shader variant keys,
pipeline layout compatibility, SIMD width, memory alignment, backend feature
flags, CUDA kernel specialization choices, or WebGPU bind layout facts.

Provider state must be keyed by provider id, backend kind, target triple, session
mode, and policy hash. `ManagedShared` and `PerfExclusive` providers must not
share mutable state.

## Qualcomm Vulkan Graphics Profile
Qualcomm graphics support is modeled as an Adreno profile over Vulkan, not as a
Metal backend. Current profile keys:

- `qualcomm-adreno:vulkan:arm64`
- `qualcomm-adreno:vulkan:arm32`
- `qualcomm-adreno:vulkan:arm32+arm64`

ARM32 and mixed ARM32/ARM64 entries are preparation profiles. Runtime support
still depends on OS, driver, loader, and executable-memory/JIT availability.

## ARM Mixed JIT
ARM mixed JIT is a facade over explicit ARM64 (`aarch64`) and ARM32 (`arm32`)
JIT handles. It provides width-dispatched compile, call, and query helpers while
keeping architecture-specific code generation, executable mapping, and icache
flush rules separate.

Policy:
- Release/native link path should prefer LLVM-compatible object generation.
- Debug/dev can keep Cranelift path.
- SMF metadata/flags must carry enough backend/PIC info so loader/linker can enforce compatibility.
- `ObjectProvider.prefer_backend` is enforced behavior, not advisory config.
- `--fixed-be` maps to the LLVM-fixed validation path used by builds and linker tests.

## Simple Optimization Plugin
Simple Optimization Plugin is the named extension point for reusable compiler and interpreter optimizations.

- It packages a semantics-preserving optimization provider so similar Simple programs can gain performance without per-application ad hoc rewrites.
- It applies before or around backend lowering: syntax normalization, HIR, MIR, pattern idioms, interpreter dispatch, and backend-independent metadata.
- It is not the same thing as an LLVM pass plugin. A Simple Optimization Plugin may improve LLVM IR quality, but LLVM still owns the standard IR optimizer and CPU backends.
- Hot and bootstrap-critical providers should be built into the compiler/interpreter.
- Optional, experimental, or out-of-tree providers may load dynamically only through a stable manifest and ABI.
- Providers must declare facts they require and facts they produce; they must not lie about overflow, aliasing, non-nullness, or target layout.

See:
- `doc/07_guide/compiler_optimization_plugin.md`
- `doc/04_architecture/compiler/simple_optimization_plugin.md`
- `doc/06_spec/app/compiler/feature/simple_optimization_plugin_spec.md`

## Fully shared frontend
Frontend must be one shared implementation: Lexer -> Treesitter -> Parser.
No duplicated parser logic in interpreter, loader, or compiler.

### Shared pipeline
1. Lexer creates normalized tokens (same keyword and trivia rules).
2. Treesitter builds stable concrete syntax tree (CST).
3. Parser converts CST to shared AST/HIR entry model.

### Consumers
- Compiler, loader, local interpreter, and remote interpreter all consume the same AST/HIR contract.
- Feature flags only change backend/runtime behavior, not frontend syntax behavior.

### Where specialization is allowed
- After frontend output: lowering, optimization, codegen, loading, execution.
- Runtime-specific validation can be added after parse step, but must not fork grammar rules.

### Rule for logic sharing
- If logic is syntax/structure related, place it in frontend layer.
- If logic is runtime/link/load related, place it after frontend layer.
- This keeps one language behavior and avoids drift between tools.

### Frontend ownership boundary (must share)
- Keyword table, operator precedence/associativity, and token kinds are single source.
- Indentation/newline/trivia normalization is single source.
- CST node shape and AST/HIR entry conversion rules are single source.
- Parse diagnostics format (file/line/column/message) is single source.

### What must NOT happen
- Interpreter must not have private keyword or grammar branch.
- Loader/linker must not parse custom syntax with duplicated rules.
- Tooling parsers can be lightweight scanners, but they must not redefine language grammar.

### Extension workflow for new syntax
1. Add token/keyword once in shared lexer definitions.
2. Add CST handling once in shared Treesitter layer.
3. Add AST/HIR lowering once in shared parser layer.
4. Add/update shared tests for tokenization, CST, parse output, and diagnostics.
5. Only then add backend/runtime behavior (lowering/codegen/interpreter/load).

### Compatibility and rollout rule
- Old and new frontend versions must both parse existing code during migration window.
- If behavior changes, version the feature gate at frontend boundary, not in runtime.
- Remove temporary forks after migration; keep one final shared path.

### Done checklist (frontend sharing complete)
- Same source text produces same AST/HIR for compiler and interpreter path.
- Same syntax error gives same diagnostic message and location in all consumers.
- No duplicated parser grammar file exists for Simple core language.
- CI includes cross-path parse parity tests.

### Minimal flow contract (reference)
```text
source -> shared lexer -> shared treesitter(CST) -> shared parser(AST/HIR)
      -> (compiler lower/codegen) OR (interpreter eval) OR (loader/link path)
```

### Current shared entrypoints (2026-02-18)
- Core frontend runner: `src/compiler_core/frontend.spl`
- Full frontend runner: `src/compiler/frontend.spl`
- Core consumers now call shared core frontend entrypoints:
  - `core_frontend_parse_reset`
  - `core_frontend_parse_append`
  - `core_frontend_parse_isolated`
- Full compiler driver now calls `parse_full_frontend` instead of inlining phase 2 logic.


## Boostrap
Bootstrap made by 5 step. 
1. seed: which is written in C++ and can compile Seed Simple Grammar with clang/LLVM.
It impled with C++20 Clang-20.
2. core: Pure simple implementation of simple. It can compile core grammar simple code.
  2-1. core1: it is compiled by seed.
  2-2. core2: it is compiled by core1
It impled with seed simple grammar.
3. full: It is simple with all feature. It can compile full grammar simple code.
  3-1. full1: it is compiler by core2
  3-2. full2: it is compiled by full1
It impled with core simple grammar.
Development is cmake/ninja based.

## SStack
SStack (Superpowers + GSD + GStack) is the unified development pipeline orchestrator.
It combines BDD/TDD spec-first workflow (Superpowers), sub-40% context budget per phase with fresh agents (GSD), and specialized role agents with data flow pipeline and quality gates (GStack).
Runs 8 phases: dev, research, arch, spec, implement, refactor, verify, ship.
State file at `.sstack/<feature>/state.md` is the sole communication channel between phases.
Integrates cooperative workflow: Phases 2-3 delegate to Codex/Gemini when available, fall back to Claude solo with notification when unavailable or quota-exceeded.

## Dev Workflow
`/dev` is an alias for `/sstack`. Same 8 phases, same state file, same quality gates, same cooperative workflow.
No separate phase definitions — just a thin redirect.

## SPipe
SPipe is the BDD (Behavior-Driven Development) test framework for Simple.
Uses `describe`/`it`/`expect` blocks with built-in matchers. Integrated into sstack Phase 4 (spec-first, before implementation).
Coverage markers: `# @cover src/path/to/impl.spl <pct>%`.

## Cooperative Workflow
Multi-LLM pipeline integrated into SStack. Phases 2-3 can use Codex (`/research_codex`) and Gemini (`/gemini_ui_design`) for richer output.
Pipeline never blocks on missing providers — every phase is self-sufficient with Claude alone.
Availability detected at runtime; fallback logged in state file as `> [!NOTE]`.

## Deployment Coverage check
"@deplyment_coverage" is tagged testcase.
It run 2 times.
1. all selected deployment coverage testcases are run first.
when it run callback coverage verifier to runner.
actually it is logged as deployment coverage test loading step.
2. when all none deployment coverage test are ran, it run callback coverage verifier.
it will be showed deployment coverage test running step.
will result by coverage verifier.
Test runner to check file coverage which deployment coverage testcase monitoring to gen coverage on different directories.
before to go 2. step, make link files to overall coverage directory and make each depoyment coverage tests directoy and make link on there.
It can specify coverage listen target by file(however it not specify filename self but module path), and threashold by file or class.
```simple
# @deplyment_coverage
describe "Parser deplyomeent coverage":
  it "should cover LLVMBackend":
    val parser_test = test_group([test.parser.*])
    parser_test.check_coverage(core.parser.llvm_backend.FILE, 50/*branch coverage*/) # it make coverage check callback and register llvm_backe.spl to generate coverage.
  it "should cover CranliftBackend codegen class":
    val cranlift_backend_test = test_group([test.parser.cranlift_backend.*])
    cranlift_backend_test.check_coverage(core.parser.cranlift_backend.FILE, 50, core.parser.cranlift_backend.Codegen.class) # it check Codegen class coverage.
    creanlift_backend_test.check_coverage(.....)


```

---

## Simple Gui Texture Tree Interface (SGTTI)

Unified read-only interface for inspecting GUI state as a texture/widget tree
hierarchy. SGTTI normalizes surfaces from four sources — TRACE32 text windows,
Simple UI access snapshots, host WM top-level windows, and **SimpleOS compositor
surfaces** — into one `WinTextSnapshot` tree that the `win_text_access` core
exposes through snapshot/query/action operations.

Consumers access SGTTI through the `play_wm_text_*` MCP tools or the
`win_text_*` API in `common.ui.win_text_access`. Each source produces
`UiAccessNode` trees with source-specific props; the shared query/action layer
handles filtering, find, and routing uniformly.

The compositor source (`WIN_TEXT_SOURCE_COMPOSITOR`) bridges `Compositor`
surfaces into access nodes, including in **hidden WM mode** where the compositor
populates its surface tree without rendering to a display backend — enabling
headless GUI testing.

Key paths:

- **Common core:** `src/lib/common/ui/win_text_access.spl`
- **Compositor adapter:** `src/os/compositor/gtti.spl`
- **WM hidden mode:** `src/os/compositor/wm_core.spl` (`WM_MODE_HIDDEN`)
- **MCP tools:** `src/app/mcp/main_lazy_play_tools.spl` (`play_wm_text_*`)
- **Hub re-exports:** `src/lib/common/ui/access.spl`

---

## MDSOC+ (Architecture)

**MDSOC outer + ECS business layer.** Default architecture for SimpleOS userland services and apps since 2026-04-17. The MDSOC capsule boundary (manifest, ports, capabilities, lifecycle) stays unchanged; inside a capsule, mutable domain state is modelled with an ECS `World`. Kernel (`src/os/kernel/`) and drivers (`src/os/drivers/`) stay MDSOC-only and do **not** use ECS. See `mdsoc_architecture_tobe.md#mdsoc-plus-ecs-business-layer`.

## ECS (Entity-Component-System)

The internal business-state model used inside every MDSOC+ capsule. Three elements:

- **Entity** — opaque `u64` identifier with a generational index; stable for its lifetime. Holds no data itself.
- **Component** — POD struct stored in a `ComponentStore<T>` column (struct-of-arrays layout). A process, socket, or window is the *union* of components attached to its entity; there is no "Process class".
- **System** — free function `fn sys_name(world: &mut World, dt: Duration)` that runs typed queries over the world and mutates matching entities.

ECS replaces inheritance-style struct nesting. Composition via components is the whole point (and CLAUDE.md forbids inheritance anyway).

## World (ECS)

The per-capsule container of entities, component stores, and a system schedule. Each userland service owns exactly one `World`. Imports via `use std.ecs`. Defined in `src/lib/nogc_sync_mut/ecs/world.spl` (sync-mutable variant) and `src/lib/gc_async_mut/ecs/world.spl` (GC-friendly variant).

## Query (ECS)

Compile-time typed iterator over entities that carry a given component tuple. Example: `world.query::<(Pid, ExitStatus)>()` yields every process entity that has both `Pid` and `ExitStatus` components. Filters include `With<T>`, `Without<T>`, and change-detection markers `Added<T>`, `Changed<T>`, `Removed<T>`.

## ComponentStore (ECS)

The per-component dense column that backs a `World`. Struct-of-arrays layout for cache efficiency: `ComponentStore<T>` holds a `dense: [T]` array + sparse entity→slot index. Adding a component appends; removing swaps-with-last. Defined in `src/lib/nogc_sync_mut/ecs/component_store.spl`.

## Change Detection (ECS)

`Added<T>`, `Changed<T>`, `Removed<T>` tick flags on components, used by the Reincarnation Server (RS) to snapshot only the modified slice of a capsule's World during state transfer across a restart. Defined in `src/lib/nogc_sync_mut/ecs/change_detection.spl`.

Cross-ref: MDSOC capsules in `src/os/services/**` and `src/os/apps/**` use ECS for internals; kernel capsules in `src/os/kernel/**` and driver capsules in `src/os/drivers/**` do not.

## RenderBackendCore (Engine2D)

The minimum required interface for a 2D rendering backend. Contains 12 methods: lifecycle (`init`, `shutdown`, `present`), identity (`name`, `width`, `height`), readback (`read_pixels`), clipping (`set_clip`, `clear_clip`), and three irreducible drawing primitives (`clear`, `draw_rect_filled`, `draw_image`). Any backend implementing only Core gets full advanced rendering via the stateless emulation layer. Defined in `src/lib/gc_async_mut/gpu/engine2d/backend_core.spl`.

## RenderBackendAdv (Engine2D)

Optimized operations that backends SHOULD implement natively for performance but CAN omit. Contains 23 methods across 7 categories: shapes (`draw_rect`, `draw_line`, `draw_circle`, `draw_circle_filled`, `draw_rounded_rect`, `draw_triangle_filled`, `draw_ellipse`, `draw_ellipse_filled`, `draw_arc`, `draw_bezier`, `draw_polygon_filled`, `draw_polyline`), thick outlines (`draw_rect_thick`, `draw_circle_thick`, `draw_rounded_rect_outline`), gradients (`draw_gradient_rect`, `draw_gradient_rect_h`, `draw_radial_gradient`), text (`draw_text`, `draw_text_bg`), alpha blending (`draw_rect_blend`, `draw_image_blend`), and scaled image (`draw_image_scaled`). Every method is statelessly emulatable from RenderBackendCore. GPU backends implement these as dedicated compute kernels; minimal backends skip them. Defined in `src/lib/gc_async_mut/gpu/engine2d/backend_adv.spl`.

## Stateless Emulation Layer (Engine2D)

A set of standalone `emu_*` functions that implement every RenderBackendAdv operation using only RenderBackendCore methods. **Stateless** means: no mutable module state, no caches, no internal buffers — each function takes the core backend + operation parameters, composes Core calls, and returns. Algorithms: Bresenham (lines), midpoint (circles/ellipses), scanline fill (triangles/polygons), De Casteljau (bezier), row/column lerp (gradients), distance-based lerp (radial gradient), Porter-Duff src-over (alpha blend), nearest-neighbor resample (scaled image), bitmap font iteration (text). Defined in `src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl`.

## GpuFfiMode (Engine2D)

Enum with two variants: `Static` (extern fn resolved at link time against the runtime) and `Dynamic` (DynLib.load via host `dlopen` at runtime). For the pure GUI SMF dynlib release path, raw host `Dynamic` loading is diagnostic/compatibility only: the default GUI artifact is an SMF dynlib package (`loader=smf_dynlib`, `dynload=smf_dynlib`) and hosted macOS/Linux adapters use SFFI only to call the extracted SMF payload (`host_dynload=sffi`). SimpleOS uses the SMF loader path for the same artifact contract; full raw shared-object mapping remains separate from GUI release acceptance. Defined in `src/lib/gc_async_mut/gpu/engine2d/ffi_dispatch.spl`.

## SReplay

Simple Replay Debugger. A deterministic replay and reverse debugging system spanning 6 tracks: QEMU full-system replay, SimpleOS kernel event log, process-level rr, Simple language semantic trace, container checkpoint/replay, and Simple-native VM replay. All tracks share the `ReplayBackend` trait and unified trace format. Guide: `doc/07_guide/sreplay.md`. Core library: `src/lib/nogc_sync_mut/replay/`.

## ReplayBackend (SReplay)

Shared trait implemented by all 6 SReplay tracks. Defines the interface for `start_recording`, `start_replay`, `stop`, `save_checkpoint`, `restore_checkpoint`, `list_checkpoints`, `reverse_step`, `reverse_continue`, and `session_info`. Defined in `src/lib/nogc_sync_mut/replay/backend.spl`.

## ReplayConfig (SReplay)

Configuration struct for replay sessions. Contains target architecture (`Arch`), mode (Record/Replay), kernel path, trace file path, QEMU machine type, memory size, GDB port, QMP socket path, and extra arguments. Defined in `src/lib/nogc_sync_mut/replay/types.spl`.

## Reverse Execution (SReplay)

NOT literal backward instruction execution. SReplay reverse debugging works by: (1) finding the nearest checkpoint before the target, (2) restoring that checkpoint, (3) replaying forward to the target event. Exposed via GDB MI `reverse-step`/`reverse-continue` and DAP `stepBack`/`reverseContinue`.

## Checkpoint (SReplay)

A saved snapshot of execution state (registers, memory, ring buffer position) that enables fast restore during replay. QEMU checkpoints use QMP `savevm`/`loadvm`. Process checkpoints use page-level CoW via `/proc/<pid>/pagemap`. Baremetal checkpoints store cycle count, PC, SP, and ring buffer state.

## Semantic Trace (SReplay)

Compiler-generated debug events injected at MIR level (Track 4). Four instrumentation levels: `none` (production), `functions` (enter/exit), `objects` (+ alloc/drop/move), `full` (+ variable writes, borrows, async). Injected by `src/compiler/50.mir/mir_debug_trace_injection.spl`. Controlled by `--debug-trace` flag.

## Chaos Scheduler (SReplay)

Process-level replay scheduler (Track 3) with 4 strategies: RoundRobin, Random, YieldHeavy, StarvationProbe. Used with `simple record --chaos ./app` to expose concurrency bugs by randomizing thread scheduling. Defined in `src/lib/nogc_sync_mut/replay/process/chaos_scheduler.spl`.

## Divergence Detection (SReplay)

Kernel replay verification (Track 2). Compares recorded events against live execution during replay. Reports mismatches as `DivergenceRecord` with kind (ScheduleMismatch, SyscallResultMismatch, TimerValueDrift, etc.), expected/actual values, and cycle count. Defined in `src/os/kernel/replay/divergence.spl`.

## Event Ring Buffer (SReplay)

Fixed-size pre-allocated ring buffer for recording nondeterministic events. Kernel version uses BSS allocation (64K entries, no heap). Baremetal version stores kind, timestamp, val_a, val_b per entry. FIFO order. Defined in `src/os/kernel/replay/log_buffer.spl` (kernel) and `src/lib/nogc_async_mut_noalloc/replay/bm_replay_core.spl` (baremetal).

## Trace Package (SReplay)

Unified trace format (`.sr/` directory) shared across all 6 tracks. Contains: `manifest.sdn` (metadata), `events/` (compressed event streams), `payloads/` (large binary data), `checkpoints/` (register state + memory deltas), `indexes/` (B-tree indexes for memory writes, source lines, object history, schedule). Defined in `src/lib/nogc_sync_mut/replay/trace_format.spl`.

## Address (SReplay)

Architecture-neutral address representation: `struct Address { bits: i32, value: i64 }`. The `bits` field is 32 or 64; upper bits are zero for 32-bit targets. Never use raw pointers in trace formats. Defined in `src/lib/nogc_sync_mut/replay/types.spl`.

## Simple DB

Two-tier database system written in Simple (formerly codenamed **spostgre**).

**Simple DB Embedded** (stdlib) — lightweight embedded database for compiler metadata and app-level table storage. Ships with every Simple installation. SDN format, atomic file I/O, QueryBuilder, string interning. No server required.

**Simple DB Full** (example) — PostgreSQL-compatible storage engine. Keeps PostgreSQL's conceptual model — 8 KiB pages, MVCC via `xmin`/`xmax`, HOT chains, WAL-first durability, TOAST — but replaces the physicalization layer with append-only NVFS arenas. Architecture follows MDSOC+ (capsule + internal ECS): eight systems (`sys_commit`, `sys_wal_flush`, `sys_checkpoint`, `sys_vacuum`, `sys_buffer_evict`, `sys_pmap_publish`, `sys_blob_gc`, `sys_capability_probe`) over component entities.

**Shared interface** (`simple_db_if`) — trait contracts both tiers implement. Application code targets these traits and can swap between embedded and full backends.

Key paths:

- **Shared traits:** `src/lib/nogc_sync_mut/simple_db_if/`, `src/lib/gc_async_mut/simple_db_if/`
- **Embedded (stdlib):** `src/lib/nogc_sync_mut/database/` — BugDB, TestDB, FeatureDB, QueryBuilder, atomic I/O
- **Full engine (submodule):** `examples/11_advanced/simple_db/` → `https://github.com/ormastes/simple-spostgre.git`
- **DBFS tests:** `test/02_integration/storage/dbfs/` — btree, pager, WAL, checkpoint, intent log, NVMe, capability, recovery
- **Research:** `doc/01_research/simple_db_research.md`
- **Design:** `doc/05_design/simple_db_design.md`, `doc/05_design/nvfs/from_simple_db.md`
- **Accel / SIMD:** `doc/05_design/simple_db_shared_accel_simd.md`
- **Feature requests:** `doc/08_tracking/feature/simple_db_requests.md`
- **Guide:** `doc/07_guide/simple_db.md`

## DBFS (Database Filesystem)

A filesystem that uses database techniques (B-tree indexing, WAL journaling, page-level checkpointing, intent logging) to manage metadata and file nodes. Similar to how btrfs uses B-trees for filesystem metadata. Backed by NVFS arenas with NVMe passthrough support. DBFS is primarily a filesystem component — it applies DB logic to file/inode management. Because it uses DB-like data structures internally, it also provides a DB-optimized storage path that Simple DB Full can leverage for its page/WAL/index operations, sharing primitives rather than duplicating them. Tests in `test/02_integration/storage/dbfs/`. Design in `doc/03_plan/nvfs_dbfs_real_filesystem.md`.

## SDN (Simple Data Notation)

Human-readable, version-control-friendly data format used by all Simple database modules. Analogous to JSON but with richer type annotations. All `*.sdn` files use atomic file I/O (shared read locks, exclusive write-rename pattern) to prevent corruption. Core infrastructure: `StringInterner` (20–40% space savings), `SdnTable`/`SdnRow` (in-memory table), `QueryBuilder` (fluent filter/sort/limit API). Defined in `src/lib/nogc_sync_mut/database/core.spl`.

---

# Simple RISC-V RTL Vocabulary

The Simple compiler includes a VHDL backend that compiles `.spl` source into synthesizable VHDL-2008. This enables writing RISC-V CPU cores, SoC peripherals, and complete systems in Simple, then deploying them to FPGA or simulating with GHDL. The following terms define this hardware pipeline.

## RTL (Register Transfer Level)

Hardware description at the register-and-combinational-logic abstraction. In Simple, RTL modules are `.spl` files that use only the VHDL synthesizable subset (integers, Bool, fixed-size Array, Struct, Enum — no floats, pointers, heap, GC). Pure functions represent combinational logic; state-returning functions represent clocked (sequential) logic. Defined in `src/lib/hardware/rv32i_rtl/` and `src/lib/hardware/rv64gc_rtl/`.

## VHDL Backend

The compiler backend that lowers MIR to VHDL-2008 entity/architecture pairs. Each function becomes one VHDL entity. The backend enforces the VHDL Hardware Subset Contract: floating-point, pointers, dynamic allocation, and runtime features produce hard compile errors. Defined in `src/compiler/70.backend/backend/vhdl/`. Contract documented in `doc/04_architecture/hardware/vhdl_hardware_subset_contract.md`.

## VHDL Hardware Subset Contract

The exact set of Simple constructs that produce valid synthesizable VHDL. Supported: integer types (i8–i64, u8–u64), Bool, fixed-size arrays, structs (records), enums, arithmetic/comparison/bitwise operators, combinational/clocked/async-reset processes, component instantiation. Unsupported (hard error): floats, Unit, pointers, dynamic arrays, heap, GC, closures, polymorphism.

## RV32I RTL Capsule

The Simple-source RISC-V 32-bit base integer core. A single-cycle Harvard architecture translated from handwritten VHDL references into `.spl` that compiles through the VHDL backend. Modules: `pkg` (constants), `alu` (combinational ALU), `decode` (instruction decoder), `regfile` (32×32 register file), `lsu` (load/store unit), `core` (datapath top), `csr` (M-mode CSR file), `trap` (trap controller), `mmu_sv32` (Sv32 page table walker), `csr_s` (S-mode CSR extension). Defined in `src/lib/hardware/rv32i_rtl/`.

## RV64GC RTL Capsule

The 64-bit RISC-V core variant with G extensions (IMAFDC) and C (compressed). Widens all RV32I modules to 64-bit datapaths, adds W-suffix instructions (ADDW, SUBW, etc.), M extension (mul/div), A extension (LR/SC atomics), and Sv39 three-level MMU. Defined in `src/lib/hardware/rv64gc_rtl/`.

## SoC RTL Capsule

System-on-Chip peripherals and bus fabric, all written in Simple RTL:
- **UART16550** — 16550-compatible UART with 16-byte TX/RX FIFOs, baud rate generator, DLAB support. `soc_rtl/uart16550.spl`
- **CLINT** — Core-Local Interrupt controller with 64-bit `mtime` timer and `mtimecmp` comparator. `soc_rtl/clint.spl`
- **PLIC** — Platform-Level Interrupt Controller, 32 sources, priority/enable/claim-complete. `soc_rtl/plic.spl`
- **Boot ROM** — 4KB fixed ROM at 0x00001000 containing LUI+JALR jump to RAM. `soc_rtl/bootrom.spl`
- **RAM** — Synchronous SRAM model (BRAM on FPGA) with byte-enable sub-word writes. `soc_rtl/ram.spl`
- **Wishbone Interconnect** — Wishbone B4 classic bus fabric, 1 master N slaves, address-decoded. `soc_rtl/wb_interconnect.spl`
- **Mailbox** — GHDL test proof peripheral for simulation pass/fail signaling. `soc_rtl/mailbox.spl`
- **SoC Top** — Wires core + bus + all peripherals. Single-tick function = one clock cycle. `soc_rtl/soc_top.spl`

Defined in `src/lib/hardware/soc_rtl/`.

## Wishbone Bus

The on-chip interconnect protocol used by the Simple RTL SoC. Wishbone B4 classic with address decoding that maps the QEMU `virt` memory layout: Boot ROM (0x00001000), CLINT (0x02000000), PLIC (0x0C000000), UART (0x10000000), RAM (0x80000000), Mailbox (0x80FF0000).

## GHDL Simulation

Open-source VHDL simulator used for gate-level verification of Simple-generated RTL. The repo has 19+ GHDL runner scripts and testbenches covering RV32/RV64 smoke, boot, mailbox, semihosting, interrupts, Sv39, and Linux handoff. Runner defined in `src/lib/nogc_async_mut_noalloc/baremetal/ghdl_runner.spl`. Testbenches in `examples/09_embedded/fpga_riscv/rtl/tb_*.vhd`.

## Semihosting (RTL)

A 3-instruction magic sequence (`SLLI zero,zero,0x1f` → `EBREAK` → `SRAI zero,zero,0x7`) that the RTL core detects to perform host I/O during simulation. Used for GHDL test output (SYS_WRITEC for char output, SYS_EXIT for halt). The `core.spl` tracks a `semi_phase` FSM and captures a0/a1 register values as operation/parameter.

## Mailbox Protocol

MMIO-based proof channel for GHDL simulation tests. Software writes command (PUTC/EXIT/RESULT) + arguments to the mailbox at 0x80FF0000, then writes trigger magic (0x0000DEAD). The testbench monitors trigger and checks results. Spec in `doc/04_architecture/hardware/ghdl_rv32_mailbox_protocol.md`. Constants in `rv32i_rtl/pkg.spl`.

## FPGA Synthesis Flow

The pipeline from Simple source to FPGA bitstream: Simple `.spl` → VHDL backend → `.vhd` files → Vivado synthesis → bitstream. Orchestrated by `riscv_fpga_linux.spl` (board profiles), `synthesis_wrapper.spl` (TCL generation), `xdc_gen.spl` (pin/timing constraints). Vivado TCL scripts in `examples/09_embedded/fpga_riscv/build*.tcl`.

## Kria K26 (FPGA Target)

Xilinx Zynq UltraScale+ SoM (xck26-sfvc784-2LV-c) used as the primary FPGA deployment target. Features PS (Processing System) with hardened ARM cores and GEM (Gigabit Ethernet MAC), and PL (Programmable Logic) for the Simple RTL SoC. PL clock derived from PS via EMIO. PS-PL bridge uses AXI4-Lite ↔ Wishbone adapter. Support in `src/lib/hardware/fpga_k26/`.

## Behavioral Model vs RTL Module

Two representations of the same hardware in the codebase:
- **Behavioral model** (`src/lib/hardware/riscv_common/`): Software emulator using standard Simple (dynamic arrays, traits, full i64 arithmetic). Used for testing and reference. NOT synthesizable.
- **RTL module** (`src/lib/hardware/rv32i_rtl/`, `rv64gc_rtl/`, `soc_rtl/`): Synthesizable Simple restricted to the VHDL hardware subset. Pure functions = combinational logic, state-update functions = clocked logic. Compiles to VHDL-2008.

## Baremetal Server Stack

The software stack that runs on the RTL SoC (or QEMU) to serve HTTP:
- **Boot chain**: `_start` (asm) → `boot_main` → `riscv_boot_mem_init` (PMM + heap) → `os_main` → `start_http_server_baremetal`
- **TCP shim** (`src/os/kernel/net/tcp_shim.spl`): Bridges `rt_io_tcp_*` extern functions to the pure-Simple netstack service
- **IoDriver shim** (`src/os/kernel/net/driver_shim.spl`): Bridges the completion-based IoDriver model (submit/poll) to cooperative netstack polling
- **Thread shim** (`src/os/kernel/net/thread_shim.spl`): Single-core stubs (thread_create returns -1, cpu_count returns 1)
- **TLS shim** (`src/os/kernel/net/tls_shim.spl`): Embedded DER certificates, fake clock, LCG entropy for baremetal TLS
- **HTTP launcher** (`src/os/kernel/net/http_baremetal.spl`): Creates single inline Worker, registers app handlers, runs the event loop

## Three-Layer Verification

The validation strategy for the RISC-V RTL + SimpleOS system:
1. **GHDL** — gate-level RTL simulation, proves hardware correctness
2. **QEMU** — ISA-level emulation with virtio devices, proves OS + server stack
3. **FPGA (Kria K26)** — real hardware execution, proves deployment readiness

Each layer validates the next: GHDL proves RTL matches spec, QEMU proves software works on the ISA, FPGA proves the synthesized RTL runs the software.
