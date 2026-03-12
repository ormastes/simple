# MDSOC Architecture For Simple

## Purpose

This document defines a layered MDSOC view for the Rust Simple workspace with emphasis on `common`, `compiler`, `loader`, `runtime/loader`, `driver`, and the interpreter path inside `compiler`.

It covers:

1. current layer mapping
2. to-be tree encapsulation
3. common tree-node extraction
4. sibling-private versus tree-private guidance

## Research Result

### 1. Tree-private is the right default

Current Simple architecture docs already lean this way:

- `doc/architecture/overview.md` says shared contracts belong in `src/common/`
- `doc/architecture/glossary.md` says compiler, loader, and interpreter must share one frontend contract
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

## Migration Sequence

1. Extract shared tree nodes to `common`.
2. Turn loader/runtime duplicates into facades.
3. Redirect compiler imports to `common`.
4. Keep interpreter/frontend grammar single-source.
5. If a future sibling-friend rule is still needed, add it as manifest/module metadata first, not syntax.
