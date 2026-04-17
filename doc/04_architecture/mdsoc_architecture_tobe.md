# MDSOC Architecture For Simple

## Purpose

This document defines a layered MDSOC view for Simple.

**Part 1 — Pure Simple** (current, self-hosted compiler): shared tree nodes across numbered layers (`00.common` → `99.loader`).

**Part 2 — Rust Bootstrap** (legacy reference): shared tree nodes across the Rust workspace (`common`, `compiler`, `loader`, `runtime`, `driver`).

It covers:

1. current layer mapping
2. to-be tree encapsulation
3. common tree-node extraction
4. sibling-private versus tree-private guidance

---

# Part 1 — Pure Simple Compiler

## Layer List

| Layer | Name | Responsibility |
|---|---|---|
| 00 | Common | Error types, config, effects, visibility, diagnostics, DI |
| 10 | Frontend | Lexer, parser, AST, tokens, treesitter, desugar |
| 15 | Blocks | Block definition system |
| 20 | HIR | HIR types, definitions, lowering, inference |
| 25 | Traits | Trait def, impl, solver, coherence, validation |
| 30 | Types | Type inference, type system, dimension constraints |
| 35 | Semantics | Semantic analysis, lint, macro check, resolve, const eval |
| 40 | Mono | Monomorphization, instantiation |
| 50 | MIR | MIR types, data, instructions, lowering, serialization |
| 55 | Borrow | Borrow checking, GC analysis |
| 60 | MIR Opt | MIR optimization passes |
| 70 | Backend | Backends (LLVM, C, Cranelift, WASM, CUDA, Vulkan, Native), linker |
| 80 | Driver | Driver, pipeline, project, build mode, incremental |
| 85 | MDSOC | Virtual capsules, feature/construct dimensions, weaving |
| 90 | Tools | API surface, coverage, query, symbol analyzer, AOP |
| 95 | Interp | Interpreter, MIR interpreter, execution |
| 99 | Loader | Module resolver, loader |

## Shared Tree Nodes (Cross-Layer)

### Tier 1 — Critical Foundations (4+ consuming layers)

These are the shared tree nodes that cross the most layer boundaries. They are candidates for L0 extraction or explicit facade contracts.

| Shared Node | Source Layer | Consuming Layers | Import Count | Role |
|---|---|---|---|---|
| `hir.hir` | 20.hir | 25.traits, 30.types, 35.semantics, 70.backend, 80.driver, 85.mdsoc, 90.tools | 36 | Core HIR — foundation of entire middle-end |
| `mir.mir_data` | 50.mir | 55.borrow, 60.mir_opt, 70.backend, 90.tools | 82 | MIR data structures — highest single-module import count |
| `common.diagnostics.span` (Span) | 00.common | 10.frontend, 25.traits, 30.types, 35.semantics, 70.backend, 80.driver | 33 | Source location tracking (canonical definition) |
| `common.config` | 00.common | 10.frontend, 20.hir, 80.driver, 99.loader | ~10 | Central global configuration |

### Tier 2 — Key Interface Types (3 consuming layers)

| Shared Node | Source Layer | Consuming Layers | Import Count | Role |
|---|---|---|---|---|
| `frontend.core.ast` | 10.frontend | 20.hir, 35.semantics, 70.backend | 135 | AST representation |
| `frontend.core.tokens` | 10.frontend | 20.hir, 35.semantics, 70.backend | 200 | Token definitions |
| `mir.mir` | 50.mir | 55.borrow, 60.mir_opt, 70.backend | 19 | MIR module facade |
| `hir.hir_definitions` | 20.hir | 30.types, 70.backend, 80.driver | ~15 | HIR definition types |
| `frontend.parser_types` | 10.frontend | 25.traits, 30.types, 70.backend | ~12 | Parser output types |

### Layer Dependency Flow

```
00.common ─────────────────────────────────────────────────── (config, errors, effects, Span)
    ↓                                                              ↓
10.frontend ──────────────────────────────────────────── (AST, tokens; Span re-imported from L0)
    ↓              ↓                                          ↓
15.blocks     20.hir ──────────────────────────────── (HIR: 7 consumers)
                  ↓         ↓         ↓
              25.traits  30.types  35.semantics
                             ↓
                         40.mono
                             ↓
                         50.mir ────────────────────── (MIR: 4 consumers, 82 imports)
                          ↓       ↓
                      55.borrow  60.mir_opt
                                   ↓
                         70.backend ←←←←←←←←←←←←←← (convergence: imports HIR+MIR+frontend)
                             ↓
                         80.driver ←←←←←←←←←←←←←←← (orchestrator: imports 13 layers)
                          ↓      ↓
                      85.mdsoc  90.tools
                                   ↓
                         95.interp
                             ↓
                         99.loader
```

### Critical Narrowing Points

The pipeline has three narrowing points where many-to-few data flows converge. These are where shared tree-node contracts matter most:

| Narrowing Point | From | To | Shared Contract |
|---|---|---|---|
| AST → HIR | 10.frontend | 20.hir | `core.ast`, `core.tokens`, `Span` |
| HIR → MIR | 20.hir + 30.types + 25.traits | 50.mir | `hir.hir`, `hir.hir_definitions` |
| MIR → Backend | 50.mir + 60.mir_opt | 70.backend | `mir.mir_data` (82 imports!) |

### Most Prolific Exporters

| Layer | Exports to N layers | Key exported types |
|---|---|---|
| 10.frontend | 11 | AST, Span, tokens, parser_types |
| 20.hir | 7 | hir, hir_definitions |
| 50.mir | 6 | mir_data, mir |
| 00.common | 4+ | config, errors, effects, diagnostics |

### Most Diverse Consumer

| Layer | Imports from N layers | Role |
|---|---|---|
| 80.driver | 13 | Pipeline orchestrator |
| 70.backend | 6+ | Convergence point (needs HIR + MIR + frontend) |

## To-Be Tree Encapsulation (Pure Simple)

### Visibility Rules

Same principles as the Rust to-be, applied to numbered layers:

- **Tree-private by default**: internal modules within a layer are not exported
- **Parent-public**: a layer exports its facade types (e.g., `hir.hir` exports `HirModule`, `HirFunction`)
- **Next-layer-public**: a layer's facade is consumed by the immediately downstream layer
- **Common-node-public**: types needed by 4+ layers should be in `00.common` or have explicit facade contracts

### Extraction Candidates

| Current Location | Issue | To-Be |
|---|---|---|
| ~~`frontend.core.lexer.Span`~~ `common.diagnostics.span.Span` | ~~Used by 5+ layers far downstream~~ **DONE** — extracted to `00.common/diagnostics/span.spl` | **Completed 2026-03-12**: canonical Span in L0, `lexer_types.spl` and `block_types.spl` re-import from common |
| `hir.hir` | 7-layer fan-out — widest shared contract | Acceptable: HIR is the canonical middle-end IR; enforce facade discipline |
| `mir.mir_data` | 82 imports from backend alone | Acceptable: MIR is the canonical low-level IR; backend convergence is by design |

### Construct Dimension (Vertical Sharing)

The MDSOC construct dimension (`85.mdsoc/construct_types/`) already models vertical sharing explicitly:

- `ConstructCapsule` groups files by language construct (Func, Trait, Enum, etc.) across all layers
- `SharedBinding` tracks files that belong to multiple construct capsules
- `CrossDimensionQuery` enables intersection queries ("all trait code in layers 10-15")

This is the Pure Simple equivalent of the Rust doc's "common tree nodes" — but modeled as data rather than module re-exports.

---

# Part 2 — Rust Bootstrap (Legacy Reference)

## Research Result

### 1. Tree-private is the right default

Current Simple architecture docs already lean this way:

- `doc/04_architecture/overview.md` says shared contracts belong in `src/common/`
- `doc/04_architecture/glossary.md` says compiler, loader, and interpreter must share one frontend contract
- `src/compiler_rust/dependency_tracker/src/visibility.rs` already models visibility as ancestor-constrained

This aligns with mainstream module systems. Rust uses module/tree privacy by default. Ada supports a narrower friend-like model through private child units. C# supports explicit friend-style access with `InternalsVisibleTo`.

### 2. Sibling-private grammar is not needed now

For Simple, a new grammar keyword for sibling-private would be premature.

Why:

- the real problem in this repo is duplicated shared nodes, not missing syntax
- current enforcement can come from module layout plus documented facades
- shared frontend behavior must not fork for interpreter or loader

Recommendation:

- keep grammar unchanged
- use tree-private as the default rule
- allow sibling access only through extracted common nodes or a small parent-owned facade

## Current State Layers

### Layer list

| Layer | Responsibility | Current paths |
|---|---|---|
| L0 Shared Contracts | zero/low dependency contracts and formats | `src/compiler_rust/common/src` |
| L1 Format + Load Core | SMF layout, loader memory, package, settlement | `src/compiler_rust/loader/src`, `src/compiler_rust/runtime/src/loader` |
| L2 Frontend + Compiler Core | parser/type/HIR/MIR/codegen/interpreter | `src/compiler_rust/compiler/src` |
| L3 Execution Orchestration | run modes, CLI, boot, test, runner | `src/compiler_rust/driver/src` |

### Observed violations

| Violation | Evidence |
|---|---|
| duplicated shared tree nodes | `loader/src/smf/{header,section,symbol,reloc}.rs` equals `runtime/src/loader/smf/{header,section,symbol,reloc}.rs` |
| compiler reaching through runtime-facing SMF path | compiler used `simple_runtime::loader::smf::*` for format structs |
| sibling access pressure caused by misplaced common nodes | SMF structural types lived in loader/runtime instead of `common` |

## To-Be Layers

### 1. Layer list

| Layer | Name | Public role |
|---|---|---|
| L0 | Common Tree Nodes | stable contracts, format structs, cross-layer traits |
| L1 | Loader Tree | file/package/settlement loading behind loader facades |
| L2 | Compiler Tree | frontend, lowering, interpreter, codegen |
| L3 | Driver Tree | orchestration and user entrypoints |

### 2. Tree-level encapsulation of each layer

| Layer | Parent public | Tree private | Next-layer public |
|---|---|---|---|
| L0 Common | `common::DynLoader`, `common::ModuleRegistry`, `common::smf::*`, `common::target::*` | internal helpers inside `common` not re-exported | shared format and trait facades for loader/compiler/driver |
| L1 Loader | `loader::ModuleLoader`, `loader::LoadedModule`, `loader::Settlement*`, `loader::startup::*` | `memory/*`, package internals, relocation application internals not re-exported directly to siblings | loader facade consumed by compiler or driver |
| L2 Compiler | `compiler::CompilerPipeline`, `compiler::interpreter::*`, `compiler::smf_builder`, `compiler::linker::*` | interpreter internals, MIR/HIR lowering internals, backend internals | compiled artifacts and interpreter entrypoints used by driver |
| L3 Driver | CLI and runner surface only | startup/db/cache internals | none |

### 3. Common relative tree-node paths

These are the common nodes siblings may access:

| Common node | Path | Used by |
|---|---|---|
| dynamic loader contract | `src/compiler_rust/common/src/lib.rs` | loader, native loader, driver |
| target model | `src/compiler_rust/common/src/target.rs` | loader, compiler, runtime |
| SMF header | `src/compiler_rust/common/src/smf/header.rs` | loader, runtime/loader, compiler |
| SMF section | `src/compiler_rust/common/src/smf/section.rs` | loader, runtime/loader, compiler |
| SMF symbol | `src/compiler_rust/common/src/smf/symbol.rs` | loader, runtime/loader, compiler |
| SMF relocation | `src/compiler_rust/common/src/smf/reloc.rs` | loader, runtime/loader, compiler |

### 4. Each layer tree nodes next-layer publics

| From layer | Public to next layer |
|---|---|
| L0 Common -> L1/L2/L3 | `common::smf::*`, `common::DynLoader`, `common::ModuleRegistry`, `common::target::*`, diagnostics/protocol contracts |
| L1 Loader -> L2/L3 | `loader::ModuleLoader`, `loader::LoadedModule`, `loader::Settlement*`, package reader/writer facades |
| L2 Compiler -> L3 | `CompilerPipeline`, interpreter entrypoints, SMF builders/writers, exported compile results |
| L3 Driver -> external | CLI / runner only |

## Raw Layer Vs Common Tree Node Matrix

Each cell lists:

- `parent`: public to parent node
- `next`: public to next-layer sibling

| Raw layer | `common::smf::header` | `common::smf::section` | `common::smf::symbol` | `common::smf::reloc` | `common::DynLoader/Registry` |
|---|---|---|---|---|---|
| L0 Common | `parent`: exported by `common::smf` facade. `next`: consumed directly by loader/compiler. | `parent`: exported by `common::smf` facade. `next`: consumed directly by loader/compiler. | `parent`: exported by `common::smf` facade. `next`: consumed directly by loader/compiler. | `parent`: exported by `common::smf` facade. `next`: consumed directly by loader/compiler. | `parent`: exported by `common` root. `next`: consumed by loader/native_loader/driver. |
| L1 Loader | `parent`: re-exported through `loader::smf`. `next`: compiler and driver use common or loader facade, not loader internals. | `parent`: re-exported through `loader::smf`. `next`: same. | `parent`: re-exported through `loader::smf`. `next`: same. | `parent`: re-exported through `loader::smf`. `next`: same. | `parent`: `loader::registry` wraps common registry. `next`: driver uses loader facade. |
| L2 Compiler | `parent`: imported from common for writing/building SMF. `next`: emitted SMF files consumed by loader. | `parent`: imported from common for layout writing. `next`: emitted section tables consumed by loader. | `parent`: imported from common for symbol emission. `next`: loader resolves and relocates them. | `parent`: imported from common for relocation emission. `next`: loader applies them. | `parent`: compiler should depend on common contracts, not loader internals. `next`: driver consumes compiler outputs. |
| L3 Driver | `parent`: usually opaque. `next`: none. | `parent`: opaque. `next`: none. | `parent`: opaque. `next`: none. | `parent`: opaque. `next`: none. | `parent`: consumes loader/compiler via facade. `next`: none. |

## Refactoring Applied

### Extracted common tree nodes

Shared SMF structural nodes are now defined in:

- `src/compiler_rust/common/src/smf/header.rs`
- `src/compiler_rust/common/src/smf/section.rs`
- `src/compiler_rust/common/src/smf/symbol.rs`
- `src/compiler_rust/common/src/smf/reloc.rs`

Loader and runtime/loader now act as facade layers over these shared nodes instead of owning duplicate copies.

Compiler SMF writers now import shared SMF nodes from `simple_common::smf`, removing a runtime-facing dependency path for basic file-format structures.

## Visibility Rules

### Base rule

Tree-private by default.

### Allowed sharing

- parent-public: a node can be exported to its parent facade
- next-layer-public: a node can be exposed to the immediately consuming next layer through a documented facade
- common-node-public: if two siblings need the same node, move that node to L0 common

### Forbidden sharing

- sibling-to-sibling private imports
- interpreter-only grammar
- loader-only grammar
- duplicating file-format structs under multiple siblings

## Platform/CPU Variation Nodes

### Principle
Platform and CPU-specific code follows the same shared-tree-node pattern:
variations are children of a common root node in L0.

### Common Tree Nodes (Platform)

| Common node | Path | Used by |
|---|---|---|
| link configuration | `common/src/platform/link_config.rs` | compiler linker, native pipeline |
| C compiler detection | `common/src/platform/cc_detect.rs` | compiler linker, native pipeline |
| assembly helpers | `common/src/platform/asm_helpers.rs` | stub generator, native backend |

### Variation Structure
```
common/src/platform/
├── link_config.rs      # PlatformLinkConfig per OS (Linux, FreeBSD, macOS, Windows)
├── cc_detect.rs        # C/C++ compiler detection per OS
├── asm_helpers.rs       # Ret/jump instructions per CPU arch
├── mod.rs              # PlatformInfo + module exports
├── sysroot.rs          # Runtime library discovery
├── env.rs, fs.rs, ...  # Existing infrastructure
```

### Rules
- New OS support: add variant to `PlatformLinkConfig::for_target()`
- New CPU arch: add variant to `asm_helpers.rs`
- Consumers (compiler/linker) never use `#[cfg(target_os)]` for link config — use `PlatformLinkConfig`

## Layer Violation Fixes Applied (Pure Simple, 2026-03-12)

### L0→L1: Span Unification
- **Canonical Span** now in `00.common/diagnostics/span.spl` (renamed `column`→`col`, added `empty()`, `merge()`, desugared free functions)
- 8 files in `00.common/` updated: `error.spl`, `gc_config.spl`, `gc_boundary.spl`, `attributes.spl`, `visibility_checker.spl`, `visibility_integration.spl`, `unsafe.spl`, `volatile.spl`
- Duplicate Span removed from `10.frontend/lexer_types.spl` and `10.frontend/block_types.spl` (now re-import from common)

### L0→L7: env_get Inlined
- `config.spl` no longer imports from `compiler.backend.ffi` — inlined `extern fn rt_env_get`
- `compiler_services.spl` BackendPort import documented as orchestration bypass (depends on L2 HirModule + L7 BackendResult)

### L0→L2: HIR-Dependent Files Moved to L35
- `unsafe.spl`, `volatile.spl`, `visibility_checker.spl`, `visibility_integration.spl` moved from `00.common/` to `35.semantics/`
- These files imported HIR types (HirType, HirExpr, etc.) — they are semantic analysis passes, not common utilities
- Driver consumers updated: `80.driver/driver.spl`, `80.driver/driver_api.spl`

### Remaining Documented Bypasses
| File | Bypass | Reason |
|---|---|---|
| `compiler_services.spl` | L0→L7 (BackendPort) | Orchestration type — cross-cutting by design |
| `attributes.spl` | L0→L1 (Attribute/Expr), L0→L3 (LayoutAttr) | Parsing functions needed by L1 consumer (`spawn_analysis.spl`); split deferred |

## Migration Sequence

1. Extract shared tree nodes to `common`.
2. Turn loader/runtime duplicates into facades.
3. Redirect compiler imports to `common`.
4. Keep interpreter/frontend grammar single-source.
5. If a future sibling-friend rule is still needed, add it as manifest/module metadata first, not syntax.

---

# Part 3 — MDSOC+ (ECS Business Layer) {#mdsoc-plus-ecs-business-layer}

**Adopted:** 2026-04-17. **Scope:** default architecture for all userland services and apps; kernel and drivers stay MDSOC-only.

## Motivation

MDSOC organises **composition** (capsules, ports, dimensions) but does not prescribe how a service models its **mutable domain state**. In practice, services like PM, VFS, netstack, WM, and apps like the browser and editor accumulate long-lived collections of related records (processes, sockets, windows, tabs, documents). Modelling those as nested structs produces rigid inheritance-like hierarchies, which CLAUDE.md forbids anyway (no inheritance — composition via components).

**MDSOC+** adds **Entity-Component-System (ECS)** as the canonical way to model business state *inside* a capsule, while leaving the outer MDSOC boundary unchanged.

## Layer Rules

| Layer | Pattern | Why |
|---|---|---|
| Kernel (ring 0) | **MDSOC only** — ports, dispatch, capsule stages | ECS overhead + dynamic composition unsafe in kernel |
| Drivers | **MDSOC capsule per device, no ECS** | Drivers are IO-bound state machines, not entity graphs |
| Userland services (PM, VM, VFS, netstack, WM, DS, RS, clock, TTY, …) | **MDSOC capsule outside, ECS inside** for domain state | Processes, sockets, windows, files, FDs, connections are entities |
| Apps (shell, editor, browser, file mgr, …) | **MDSOC capsule outside, ECS inside** for domain/UI state | Scene graphs, documents, tabs, panes = entities |
| libc / POSIX shim | Neither (thin ABI veneer) | No state of its own |

## Canonical ECS Shape

- **Entity** = opaque `u64` id with generational index; stable for its lifetime.
- **Component** = POD struct stored in a `ComponentStore<T>` column (struct-of-arrays).
- **System** = free function `fn sys_name(world: &mut World, dt: Duration)` that queries component sets and mutates.
- **World** = the per-service container of entities + component stores + system schedule.
- **Query** = compile-time typed iterator over entities having a given component tuple.
- **Change detection** = `Added<T> / Changed<T> / Removed<T>` flags used by RS for state transfer across capsule restarts.

## Stdlib Target

- `src/lib/nogc_sync_mut/ecs/` — default ECS for sync-mutable services (kernel-adjacent userland).
- `src/lib/gc_async_mut/ecs/` — GC-friendly variant for async/high-allocator apps.
- Import surface: `use std.ecs` — re-exports `{World, Entity, ComponentStore, Query, System, Added, Changed, Removed}`.

## What ECS Does NOT Replace

- MDSOC capsule boundaries, manifests, and lifecycle.
- Capability tokens and IPC endpoints.
- Port contracts and typed dispatch.

ECS is strictly the **internal business-state model** of one capsule. Inter-capsule communication stays on MDSOC ports + capabilities.

## Acceptance Criteria

1. `src/lib/nogc_sync_mut/ecs/` landed with `entity / component_store / world / query / system / change_detection`.
2. ≥1 reference port (`src/os/services/wm/`) uses ECS internally and passes existing WM specs.
3. Every new userland service/app spec in `doc/06_spec/` states its World + components + systems.
4. Glossary entries for MDSOC+, ECS, Entity, Component, System, World, Query, ComponentStore exist and cross-link from MDSOC/Capsule/Port.
5. `bin/simple lint` advisory rule flags monolithic struct state in new services (advisory only, not blocking).

## UI Worked Example (WidgetNode + UISession)

The typed-core API (`doc/05_design/ui_typed_core_rfc.md`, Phases 1-6) maps directly onto the MDSOC+ shape.

| MDSOC+ concept | UI equivalent | Notes |
|---|---|---|
| **Component** | `WidgetNode` / `WidgetRecord` | Immutable description of a single widget; pure POD struct |
| **Entity** | node ID (`u64`) | Stable within a UISession; identity separate from data |
| **World** | `UISession` | Owns the entity registry + all component stores (props, style, lifecycle state) |
| **System** | `UIEventBus`, layout engine, lifecycle dispatcher | Free functions operating on the world each frame |
| **Query** | typed iterator over nodes having a prop/style component | e.g. "all nodes with `SurfaceRole.Card` and `visible=true`" |
| **Change detection** | `Added<WidgetNode>` / `Changed<WidgetRecord>` | Used to diff between frames for incremental re-render |

Lifecycle example:

```
frame N:
  UIEventBus system  →  dispatches UIEvent to matching entity
  layout system      →  queries (WidgetNode, SizeClass) → writes layout props
  render system      →  queries (WidgetNode, StyleProps) → emits draw calls
```

`WidgetNode` is the component (data). `UISession` is the world (container). Layout and event dispatch are systems (operate on the world per frame). This is the same ECS shape used by `src/os/services/wm/` and any other MDSOC+ userland service.

## Out of Scope

- Porting the kernel or drivers to ECS — explicitly disallowed.
- Dynamic component registration at runtime — Simple's type system wants static queries.
- Scripting-language reflection of ECS state — revisit when a scripting need arises.
