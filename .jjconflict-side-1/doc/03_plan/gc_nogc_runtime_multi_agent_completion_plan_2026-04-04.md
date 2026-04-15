# GC / no-GC Runtime Multi-Agent Completion Plan

**Date:** 2026-04-04  
**Status:** Draft  
**Scope:** Complete the GC / no-GC runtime-family implementation so it moves from “real but uneven” to a fully supported feature with an explicit support matrix.

## 1. Goal

Complete the runtime-family feature across:
- stdlib family parity
- compiler enforcement parity
- interpreter parity
- target preset mapping
- compiled-mode proof coverage
- support-matrix and README wording

The current problem is not lack of architecture.
The current problem is uneven closure across families and execution paths.

## 2. Completion Criteria

The feature is complete when:

1. Every public runtime family has a documented contract.
2. Compiler, interpreter, loader, and test runner agree on that contract.
3. Unsupported crossings fail clearly.
4. Target presets resolve deterministically to one runtime family or one documented fallback.
5. Each supported public family has authoritative compiled-mode tests.
6. README and docs describe exact scope, not only “GC and no-GC both exist”.

## 3. Runtime Families To Treat As First-Class Lanes

Primary lanes:
- `gc_sync_immut`
- `gc_sync_mut`
- `gc_async_mut`
- `nogc_sync_immut`
- `nogc_sync_mut`
- `nogc_async_immut`

Secondary or scoped lanes:
- `*_noalloc`
- baremetal-focused family variants
- internal-only or architecture-only families

The first phase of work must explicitly classify each family as:
- public
- advanced/scoped
- internal-only

## 4. Multi-Agent Work Breakdown

### Agent 1: Runtime Contract Audit

Ownership:
- docs and support matrix only

Primary files:
- `doc/07_guide/`
- `doc/report/`
- target/runtime family documentation

Tasks:
- define exact contract per family:
  - allocation allowed
  - mutation allowed
  - async allowed
  - concurrency model
  - FFI expectations
  - baremetal suitability
- build one authoritative matrix:
  - family
  - allocation model
  - mutability
  - concurrency
  - target suitability
  - current proof status
  - known gaps
- identify which families are public versus internal-only

Deliverables:
- runtime-family support matrix doc
- updated classification for public vs internal families

Acceptance:
- one matrix exists that the rest of the agents can implement against

### Agent 2: Compiler Enforcement Parity

Ownership:
- compiler config, diagnostics, and policy enforcement

Primary files:
- `src/compiler/`
- especially GC mode/config/boundary/target preset logic

Tasks:
- audit all `GcMode`, `GcConfig`, boundary checks, and preset resolution
- identify enforcement gaps between families
- close gaps in:
  - illegal allocation in no-GC
  - illegal cross-family imports or calls
  - boundary diagnostics
  - family inference from target/backend flags
- unify diagnostics so policy failures are explicit and stable

Acceptance:
- the same runtime-family policy applies in `check`, `build`, `compile`, and test entrypoints

### Agent 3: Interpreter Parity

Ownership:
- interpreter/runtime-family behavior

Primary files:
- `src/compiler/95.interp/`
- runtime-sensitive execution paths

Tasks:
- implement or tighten interpreter enforcement where `GcMode` is currently ignored
- reject or emulate unsupported runtime-family features consistently
- ensure interpreter does not silently accept code that compiled mode rejects
- add mode-sensitive checks for:
  - allocation
  - async mutation
  - GC-only APIs
  - no-GC-only APIs

Acceptance:
- interpreter behavior matches the documented contract for all supported public families

### Agent 4: Stdlib Family Parity

Ownership:
- stdlib runtime-family surface

Primary files:
- `src/lib/`
- all `gc_*` and `nogc_*` family trees

Tasks:
- compare exported module surface across families
- classify each difference as:
  - fully shared
  - intentionally missing
  - accidentally missing
- fill high-value missing modules for public families
- remove or clearly mark unstable exports that imply parity without proof
- make naming/layout consistent across public families

Acceptance:
- each public family has a coherent, documented, usable module surface

### Agent 5: Target Presets and Baremetal Mapping

Ownership:
- target/backend/runtime-family selection

Primary files:
- target preset modules
- build driver target resolution
- baremetal preset logic

Tasks:
- define deterministic mapping for:
  - hosted desktop targets
  - server targets
  - wasm targets
  - baremetal targets
- ensure each preset resolves one runtime family or one documented fallback chain
- eliminate ambiguous auto-selection that changes silently by host
- make `no_gc`, `no_std`, and baremetal presets explicit and testable

Acceptance:
- target preset resolution exposes the chosen runtime family in diagnostics, logs, or test-visible output

### Agent 6: Test and Proof Closure

Ownership:
- authoritative runtime-family verification

Primary files:
- `test/feature/`
- `test/integration/`
- `test/system/`

Tasks:
- build a test matrix by family covering:
  - allocation allowed/disallowed
  - mutation allowed/disallowed
  - async support
  - boundary violations
  - target preset resolution
  - interpreter vs compiled parity
- add compiled-mode authoritative proofs for each public family
- add negative tests:
  - GC API in no-GC family
  - no-GC target using GC-only feature
  - illegal cross-family imports/calls
- separate:
  - structural/load tests
  - semantic enforcement tests
  - target-preset tests
  - baremetal-family tests

Acceptance:
- every public family has at least one authoritative compiled proof
- every policy rule has at least one failing test

### Agent 7: Support Matrix and README Reclassification

Ownership:
- public wording only after proof exists

Primary files:
- `README.md`
- `doc/report/unique_features.md`

Tasks:
- replace vague “GC and no-GC runtime families exist” wording with:
  - supported families
  - supported targets
  - known limits
- classify each family as:
  - stable
  - supported with qualifiers
  - advanced/scoped
  - internal
  - experimental
- remove any parity claim not backed by tests

Acceptance:
- README wording is derivable from the support matrix

## 5. Execution Order

1. Agent 1 builds the runtime-family contract matrix.
2. Agents 2, 3, 4, and 5 work in parallel against that matrix.
3. Agent 6 starts once enforcement behavior is stable enough to prove.
4. Agent 7 updates public docs last.
5. Main agent integrates changes and runs final verification.

## 6. Critical Early Decisions

These must be answered before implementation spreads too far:

1. Which runtime families are truly public?
2. Is interpreter parity mandatory for all public families, or only a supported subset?
3. Which stdlib differences are intentional versus accidental?
4. Which target presets are authoritative for no-GC?
5. What counts as “complete” for the weakest families, especially:
   - `gc_async_mut`
   - `nogc_async_immut`

## 7. Validation Matrix

Each public family must be validated across:

- **Contract**
  - documented allocation/mutation/async behavior
- **Compiler**
  - enforcement and diagnostics
- **Interpreter**
  - parity with compiled semantics where promised
- **Stdlib**
  - coherent exported module surface
- **Target Presets**
  - deterministic resolution
- **Proof**
  - compiled-mode authoritative tests

No family should remain public if it cannot satisfy the matrix at its declared support level.

## 8. Definition Of Done

The runtime-family feature is complete when:

- every public family has a documented contract
- compiler/interpreter/presets agree
- unsupported usage fails clearly
- target mapping is deterministic
- tests prove each public family in compiled mode
- README and support matrix match repo truth

## 9. Recommended Real Agent Assignment

- Agent A: contract and docs matrix
- Agent B: compiler enforcement
- Agent C: interpreter parity
- Agent D: stdlib parity
- Agent E: target presets and baremetal mapping
- Agent F: test matrix and proof closure
- Main agent: integration, doc reclassification, final verification

## 10. Immediate Next Steps

1. Build the runtime-family contract matrix.
2. Freeze the public-family set.
3. Audit compiler enforcement parity.
4. Audit interpreter parity.
5. Build the authoritative test matrix for each public family.
