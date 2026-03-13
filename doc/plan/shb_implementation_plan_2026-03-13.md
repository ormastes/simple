# SHB Implementation Plan

Date: 2026-03-13
Status: active
Scope: SHB generation, watcher/cache integration, loader integration, interpreter lazy loading, circular dependency handling, and test coverage

## Goal

Make `SHB` the stable interface artifact for module-level lazy loading and circular import handling across:

- compiler cache generation
- watcher-triggered generation
- loader-side cache use
- interpreter deferred module loading

The end state is:

1. `SHB` is always generated from a correct parse, never from stale global AST state.
2. `SHB` interface hashes are stable and dependency-aware.
3. watcher, compiler, and interpreter all use the same SHB retrieval contract.
4. interpreter lazy loading uses SHB to avoid forcing unrelated modules.
5. circular imports compile/run through interface-first loading, then body forcing.
6. system tests prove the real wiring, not just reader/writer unit behavior.

---

## Current-State Map

### Layers

1. `src/compiler/80.driver/shb`
   Purpose: SHB format, extraction, hash, read/write, cache manager.

2. `src/compiler/80.driver/watcher`
   Purpose: freshness checks, daemon/watcher retrieval, inline fallback generation.

3. `src/compiler/99.loader/loader`
   Purpose: compiled-module loader, currently more SMF-oriented than SHB-oriented.

4. `src/compiler/10.frontend/core/interpreter`
   Purpose: runtime `use` resolution, deferred module loading, symbol forcing.

5. `src/app/dev`
   Purpose: external helper entrypoints like `shb_emit.spl`.

### Common Relative Tree Nodes

These are already effectively shared contracts and should remain common:

- `src/compiler/80.driver/shb/shb_types.spl`
- `src/compiler/80.driver/shb/shb_reader.spl`
- `src/compiler/80.driver/shb/shb_writer.spl`
- `src/compiler/80.driver/shb/shb_hash.spl`

These are current cross-layer bridge points:

- `src/compiler/80.driver/shb/shb_extractor.spl`
- `src/compiler/80.driver/shb/shb_cache.spl`
- `src/compiler/80.driver/watcher/watcher_client.spl`
- `src/app/dev/shb_emit.spl`

### Current Public Surface To Next Layer

`shb` -> watcher/compiler/interpreter
- `ShbReader`
- `shb_write`
- `shb_interface_hash`
- `external_extract_write_shb`
- `ShbCacheManager`

watcher -> loader/interpreter
- `get_or_generate_shb`
- `check_shb_freshness`
- `watcher_temp_config`

interpreter -> eval path
- `register_deferred_module`
- `force_deferred_module`
- `try_force_any_deferred_for`

### Current Violations

1. Interpreter currently depends on runtime-fragile nested-array state in:
   - `src/compiler/10.frontend/core/interpreter/value.spl`
   - `src/compiler/10.frontend/core/interpreter/env.spl`
   - plus some already-partially-fixed loader/tracker state

2. SHB dependency entries are not yet rich enough for real circular invalidation.

3. Interpreter in-process module loading is still not stable enough to complete the SHB-driven lazy path end-to-end.

4. Loader-side SHB usage is still weak; most real regeneration logic is watcher/client-centric.

---

## To-Be Architecture

### Layer List

1. `common contract layer`
   Files:
   - `src/compiler/80.driver/shb/shb_types.spl`
   - `src/compiler/80.driver/shb/shb_hash.spl`
   - `src/compiler/80.driver/shb/shb_reader.spl`
   - `src/compiler/80.driver/shb/shb_writer.spl`

2. `generation layer`
   Files:
   - `src/compiler/80.driver/shb/shb_extractor.spl`
   - `src/app/dev/shb_emit.spl`

3. `artifact orchestration layer`
   Files:
   - `src/compiler/80.driver/shb/shb_cache.spl`
   - `src/compiler/80.driver/watcher/watcher_client.spl`

4. `execution consumers`
   Files:
   - `src/compiler/99.loader/loader/module_loader.spl`
   - `src/compiler/10.frontend/core/interpreter/module_loader.spl`

### Tree-Level Encapsulation

`shb` tree-private
- binary layout details
- section encoding details
- hashing internals

`shb` public to parent
- `ShbReader`
- `ShbModuleInterface`
- persist/extract result types
- cache manager result types

`watcher` public to next-layer sibling
- artifact retrieval and freshness facade only

`interpreter` tree-private
- deferred module bookkeeping
- symbol-force policy
- runtime fallback behavior

`frontend grammar` single-source
- no interpreter-only syntax
- no watcher-specific parse mode

### Common Tree Nodes Matrix

| Raw Layer | Common Node | Public To Parent | Public To Next-Layer Sibling |
|---|---|---:|---:|
| `shb` | `shb_types.spl` | yes | yes |
| `shb` | `shb_reader.spl` | yes | yes |
| `shb` | `shb_writer.spl` | yes | yes |
| `shb` | `shb_hash.spl` | yes | yes |
| `watcher` | retrieval facade | yes | yes |
| `interpreter` | lazy-force facade | yes | no |
| `loader` | validated SHB lookup | yes | no |

---

## Required End-State Semantics

### SHB Generation Semantics

For any source module:

1. Parse source in a correct parse context.
2. Extract only public interface information.
3. Compute:
   - `source_hash`
   - `interface_hash`
4. Compute dependency interface hashes for imported modules.
5. Persist a valid `.shb`.

### SHB Retrieval Semantics

Any consumer asking for SHB must follow one contract:

1. check freshness
2. if fresh, read cached artifact
3. if watcher is available, request artifact
4. otherwise use a stable fallback generation path
5. return:
   - artifact path
   - source hash
   - interface hash
   - failure detail on error

### Interpreter Lazy Loading Semantics

For `use lazy mod.*` or `use lazy mod.{a,b}`:

1. register deferred module metadata
2. when a missing symbol is referenced:
   - first consult explicit imported names
   - then consult SHB metadata
   - skip modules that cannot define the symbol
   - force only plausible modules
3. after force-load, symbol table resolution proceeds normally

### Circular Dependency Semantics

Interface-level circular dependencies must work by:

1. allowing SHB interface generation for mutually-importing modules
2. validating against dependency interface hashes
3. permitting deferred body loading where bodies depend on each other
4. not forcing unrelated modules during a symbol lookup

---

## Work Plan

## Phase 0: Stabilize Baseline

Objective:
Make the current green watcher path the fixed baseline before deeper SHB work.

Tasks:

1. Keep watcher SHB system spec green:
   - `test/system/watcher/watcher_shb_wiring_system_spec.spl`

2. Keep runtime bug probes explicit:
   - `test/system/runtime/runtime_nested_struct_probe.spl`
   - `test/system/interpreter/interpreter_init_probe.spl`

3. Remove accidental merge/conflict text from active spec files whenever found.

Acceptance:

- watcher SHB system spec passes
- runtime probes reproduce current interpreter limitations clearly

---

## Phase 1: Make SHB Contract Canonical

Objective:
Define a single contract for SHB artifacts and retrieval.

Files:

- `src/compiler/80.driver/shb/shb_types.spl`
- `src/compiler/80.driver/watcher/watcher_client.spl`
- `src/compiler/80.driver/shb/shb_cache.spl`

Tasks:

1. Introduce or normalize one shared load result type for SHB retrieval.

2. Ensure all retrieval callers receive:
   - `ok`
   - `shb_path`
   - `source_hash`
   - `interface_hash`
   - `error`

3. Remove divergent local “empty interface” fallback behavior.

4. Document the contract in:
   - `doc/guide/tooling/shb.md`

Acceptance:

- no caller constructs invalid synthetic SHB metadata on failure
- watcher and cache manager return consistent metadata

---

## Phase 2: Finish Parse-Correct Generation

Objective:
Ensure SHB generation always comes from a reliable parse path.

Files:

- `src/compiler/80.driver/shb/shb_extractor.spl`
- `src/app/dev/shb_emit.spl`
- `src/compiler/80.driver/shb/shb_cache.spl`
- `src/compiler/80.driver/watcher/watcher_client.spl`

Tasks:

1. Keep the external generation path as the current production-safe fallback.

2. Clearly separate:
   - in-process parse/extract helpers
   - external fallback helpers

3. Mark in-process parse helpers as not production-safe for interpreter runtime until frontend init is fixed.

4. Make external emitter output format stable and machine-parsable.

5. Add explicit failure messages for:
   - parse failure
   - writer failure
   - invalid SHB readback

Acceptance:

- fresh SHB generation works from watcher path
- fresh SHB generation works from cache manager path
- generated SHB reopens as valid in production path

---

## Phase 3: Dependency Hash Correctness

Objective:
Replace placeholder dependency metadata with real dependency interface hashes.

Files:

- `src/compiler/80.driver/shb/shb_extractor.spl`
- `src/compiler/80.driver/shb/shb_cache.spl`
- `src/compiler/80.driver/cache/cache_validator.spl`
- `src/compiler/80.driver/watcher/watcher_client.spl`

Tasks:

1. Extend `extract_dependency()` to capture:
   - module path
   - resolved source path if available
   - dependency interface hash

2. Resolve imports for SHB dependency extraction through the same module path rules used by consumers.

3. For each imported module:
   - attempt to load or generate its SHB
   - record the dependency interface hash

4. Validate SHB freshness against:
   - source hash
   - interface hash
   - dependency interface hashes

5. Preserve body-only changes as non-interface invalidations when possible.

Acceptance:

- dependency entries no longer use `interface_hash: 0`
- changing a dependency interface invalidates parent SHB
- changing only a dependency body does not falsely invalidate interface-only dependents

Risks:

- recursive SHB generation loops
- import path resolution mismatches

Mitigation:

- maintain a generation stack / visited set for dependency resolution

---

## Phase 4: Circular Interface Model

Objective:
Make SHB the interface-first mechanism for circular module graphs.

Files:

- `src/compiler/80.driver/shb/shb_extractor.spl`
- `src/compiler/80.driver/shb/shb_cache.spl`
- `src/compiler/10.frontend/core/interpreter/module_loader.spl`
- `src/compiler/99.loader/loader/module_loader.spl`

Tasks:

1. Define circular-safe generation rules:
   - if module `A` needs `B`’s interface and `B` is in-progress, consume last-known-fresh SHB if valid
   - if not present, allow interface-only extraction pass without body execution semantics

2. Introduce explicit generation states:
   - missing
   - generating-interface
   - interface-ready
   - stale
   - failed

3. Prevent infinite regeneration recursion with a path stack.

4. Separate interface extraction from body-sensitive runtime loading.

5. Define exact behavior for:
   - `A <-> B` wildcard imports
   - selective imports
   - body references to symbols that require force-loading

Acceptance:

- mutually importing modules can produce SHB interfaces without recursion collapse
- interface availability does not require forcing all module bodies

---

## Phase 5: Interpreter Runtime Stabilization

Objective:
Remove the remaining interpreter runtime blockers that prevent SHB lazy loading from working end-to-end.

Files:

- `src/compiler/10.frontend/core/interpreter/value.spl`
- `src/compiler/10.frontend/core/interpreter/env.spl`
- `src/compiler/10.frontend/core/interpreter/module_loader.spl`
- `src/compiler/10.frontend/core/interpreter/interp_resource_tracker.spl`
- possibly `src/compiler/10.frontend/core/interpreter/resolve.spl`

Known blockers:

1. `val_reset()` currently fails in runtime due to nested-array mutation behavior.
2. `env_init()` still has runtime/container incompatibilities.
3. direct struct-held array and nested-array mutations are not consistently safe.

Tasks:

1. Replace nested-array `.push(...)` initialization patterns with runtime-safe representations.

2. Prefer one of these patterns consistently:
   - flattened text encoding
   - map-backed storage plus snapshot arrays
   - whole-array replacement via `arr = arr + [item]`

3. Audit interpreter globals with nested arrays:
   - value arena arrays
   - env scope tables
   - frame locals
   - resolve slot maps
   - any remaining loader/tracker arrays

4. Add minimal probes for each initializer and each hot path.

Acceptance:

- `test/system/interpreter/interpreter_import_probe.spl` passes
- `test/system/interpreter/interpreter_init_probe.spl val` passes
- `test/system/interpreter/interpreter_init_probe.spl env` passes
- `load_module()` works without runtime type corruption

---

## Phase 6: Interpreter SHB Lazy Loading

Objective:
Complete end-to-end interpreter-side SHB gating for lazy imports.

Files:

- `src/compiler/10.frontend/core/interpreter/module_loader.spl`
- `src/compiler/10.frontend/core/interpreter/eval.spl`
- `src/compiler/10.frontend/core/interpreter/eval_decls.spl`

Tasks:

1. Keep deferred-module registration lightweight.

2. On symbol miss:
   - check explicit import list first
   - consult SHB symbol membership second
   - only then force-load the module

3. Ensure wildcard imports do not force unrelated modules.

4. Ensure circular deferred modules resolve through a sequence of:
   - SHB interface filter
   - force targeted module
   - symbol table retry

5. Do not make interpreter depend on watcher daemon availability.

6. Keep fallback generation external if in-process parse path remains unstable.

Acceptance:

- unrelated wildcard deferred modules are skipped
- circular lazy wildcard case resolves without loading unrelated modules

---

## Phase 7: Loader-Side SHB Use

Objective:
Use SHB more explicitly in compiled loader flows, not only watcher flows.

Files:

- `src/compiler/99.loader/loader/module_loader.spl`
- `src/compiler/80.driver/watcher/watcher_client.spl`

Tasks:

1. Add loader-side SHB lookup helpers for interface preflight.

2. Use SHB where the loader needs interface metadata before SMF/body loading.

3. Keep loader-specific policy distinct from interpreter policy:
   - loader validates artifacts
   - interpreter filters deferred force-loads

Acceptance:

- compiled loader has a documented SHB usage path
- no direct dependency from loader into interpreter-private module state

---

## Phase 8: System Test Completion

Objective:
Replace placeholder lazy-loading specs with real wiring coverage.

Files:

- `test/system/watcher/watcher_shb_wiring_system_spec.spl`
- `test/system/interpreter/lazy_shb_system_spec.spl`
- `test/system/interpreter/lazy_shb_probe.spl`
- `test/unit/compiler/loader/use_lazy_spec.spl`

Tasks:

1. Keep watcher system spec as artifact-generation coverage.

2. Make interpreter system spec cover:
   - direct load
   - wildcard filter
   - circular wildcard

3. Downgrade or replace placeholder unit tests in:
   - `test/unit/compiler/loader/use_lazy_spec.spl`

4. Add focused failure probes:
   - parser append failure
   - runtime nested-struct regression
   - interpreter init regression

Acceptance:

- unit tests prove logic
- system tests prove wiring
- no more placeholder “expect(true)” lazy-loading coverage

---

## Phase 9: Documentation Completion

Objective:
Make the SHB architecture, contract, and operational use discoverable.

Files:

- `doc/guide/tooling/shb.md`
- `doc/guide/README.md`
- this plan file

Tasks:

1. Update guide with:
   - what SHB is
   - how it is generated
   - how watcher/compiler/interpreter consume it
   - circular dependency model
   - known runtime caveats

2. Add test references.

3. Add troubleshooting section:
   - stale SHB
   - invalid SHB
   - interpreter fallback behavior

Acceptance:

- docs match production wiring and test coverage

---

## Concrete File Checklist

### Must Change

- `src/compiler/80.driver/shb/shb_extractor.spl`
- `src/compiler/80.driver/shb/shb_cache.spl`
- `src/compiler/80.driver/shb/shb_reader.spl`
- `src/compiler/80.driver/shb/shb_hash.spl`
- `src/compiler/80.driver/watcher/watcher_client.spl`
- `src/compiler/10.frontend/core/interpreter/module_loader.spl`
- `src/compiler/10.frontend/core/interpreter/value.spl`
- `src/compiler/10.frontend/core/interpreter/env.spl`
- `src/compiler/10.frontend/core/interpreter/interp_resource_tracker.spl`

### Likely Change

- `src/compiler/99.loader/loader/module_loader.spl`
- `src/compiler/10.frontend/core/interpreter/__init__.spl`
- `src/compiler/10.frontend/core/interpreter/eval_decls.spl`
- `src/compiler/10.frontend/core/interpreter/eval.spl`

### Test Files

- `test/system/watcher/watcher_shb_wiring_system_spec.spl`
- `test/system/watcher/shb_wiring_probe.spl`
- `test/system/interpreter/lazy_shb_system_spec.spl`
- `test/system/interpreter/lazy_shb_probe.spl`
- `test/system/interpreter/interpreter_import_probe.spl`
- `test/system/interpreter/interpreter_init_probe.spl`
- `test/system/interpreter/parse_append_probe.spl`
- `test/system/runtime/runtime_nested_struct_probe.spl`

---

## Acceptance Matrix

### Artifact Generation

- cached SHB read/write works
- fresh SHB generation works
- metadata roundtrip works
- body-only versus interface-change detection works

### Dependency Handling

- dependency interface hashes are recorded
- interface-changing dependency invalidates parent SHB
- body-only dependency change does not over-invalidate

### Interpreter

- `eval_init()` passes
- direct `load_module()` passes
- deferred wildcard filter passes
- circular lazy wildcard passes

### Loader

- loader can obtain validated SHB metadata without runtime-only assumptions

---

## Suggested Execution Sequence

1. Stabilize interpreter init (`value.spl`, `env.spl`)
2. Make `load_module()` pass in direct-load probe
3. Turn interpreter lazy SHB system spec green
4. Implement real dependency interface hashes
5. Implement circular interface-generation states
6. Add loader-side SHB validation usage
7. Finish docs and remove placeholder lazy-loading tests

---

## Stop Conditions

Do not call SHB “done” until all of these are true:

1. watcher SHB system spec is green
2. interpreter lazy SHB system spec is green
3. dependency interface hashes are non-placeholder
4. circular import interface flow is explicitly tested
5. docs match the implemented production path

---

## Immediate Next Task

The next highest-value task is:

1. fix interpreter `val_reset()` runtime corruption
2. fix interpreter `env_init()` container/runtime mismatch
3. re-run:
   - `test/system/interpreter/interpreter_init_probe.spl`
   - `test/system/interpreter/lazy_shb_probe.spl`
   - `test/system/interpreter/lazy_shb_system_spec.spl`

That is the shortest path back to the remaining red SHB milestone.
