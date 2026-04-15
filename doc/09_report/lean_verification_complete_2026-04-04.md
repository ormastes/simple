# Lean Verification Completion Report

**Date:** 2026-04-04
**Status:** Complete (bounded milestone)

## Summary

Completed the Lean verification product workflow for the Simple language compiler. The implementation covers the full path from annotated Simple source code to formal Lean 4 proof obligations, including generation, checking, caching, reporting, and public documentation. All features are bounded by the contract in `doc/04_architecture/lean_verification_contract.md`.

## What Was Built

### Phase 0: Foundation Models

- **VerificationState enum** (6 states): `verified`, `failed`, `admitted`, `trusted`, `stale`, `not_checked`
- **ProofUnit model**: atomic verification tracking unit with source-to-Lean mapping, obligation list, state, fingerprint, dependency tracking, and debt counters
- **ProofUnitSet**: collection with filtering, aggregation, state counting, and dependency invalidation
- **StateCounts**: summary display with formatted output
- **Aggregation rules**: most-severe-wins rollup (`failed` > `admitted` > `trusted` > `stale` > `not_checked` > `verified`)
- **Support matrix**: full feature-by-capability table in the contract document

### Phase 1: Deterministic Lean Generation

- **LeanBackend**: MIR-to-Lean 4 export backend implementing both `Codegen` and `VerificationCodegen` traits
- **LeanBuilder**: structured Lean 4 code builder with namespaces, structures, inductives, definitions, theorems, axioms
- **MIR-to-Lean translation**: full instruction set translation (binops, unops, alloc, load, store, GEP, aggregates, casts, calls, intrinsics)
- **Type translation**: i64/i32/i16/i8/f64/f32/bool/unit/ptr/array/struct/tuple/option/result mapped to Lean types
- **Proof tactic selection**: pattern-based tactic chooser (trivial, rfl, decide, omega, simp, ring, aesop, constructor, sorry fallback)
- **Contract extraction**: pre/postcondition to Lean specification generation
- **Proof obligation model**: BoundsCheck, NullCheck, DivisionByZero, NoAliasing, ValidLifetime, LoopInvariant, Postcondition, Termination
- **Sorted emission**: deterministic output ordering for reproducible generation

### Phase 2: lean{} Block and Proof Reference Integration

- **LeanBlock model**: embedded Lean 4 code with automatic theorem name extraction, import extraction, placement levels (module/function/type), namespace support
- **Collision detection**: detects duplicate theorem names between generated obligations and handwritten lean{} blocks
- **Import deduplication**: lean{} block imports merged with generator defaults without duplicates; import lines stripped from block body
- **Proof reference resolution**: `proof uses:` references resolved against external Lean modules in `verification/proofs/`
- **Codegen integration**: `LeanCodegen.add_lean_block()` pipeline with block content emission and source attribution comments

### Phase 3: Toolchain and Proof Check Path

- **ToolchainInfo**: detection of lean/lake binaries, version extraction, lean-toolchain file comparison
- **ToolchainError enum**: LeanNotFound, LakeNotFound, VersionMismatch, ProjectInvalid, DependencyError -- distinct from proof errors
- **validate_toolchain()**: ordered environment validation with early-exit on first error
- **LeanCheckResult**: per-file result model with goals_solved/goals_remaining, sorry detection, pass/fail classification
- **VerificationSummary**: multi-file aggregation with files_checked/passed/failed, theorem counts, proven/unproven
- **Verification checker rules**: V-UNSAFE, V-EFFECT, V-REFLECT, V-GHOST, V-TRUSTED, V-PARTIAL enforcement

### Phase 4: Incremental Verification Cache

- **Fingerprint**: content hash from source + generated Lean + dependency hashes + toolchain version (FNV-1a inspired)
- **VerificationCache**: SDN-based file storage in `build/verification-cache/`, one file per source
- **Cache lookup safety invariant**: stale entries (fingerprint mismatch) are never returned
- **CacheEntry serialization**: SDN format with fingerprint, state, per-theorem results, timestamp, lean version
- **Dependency invalidation**: `invalidate_dependents()` walks proof units to find transitive dependents
- **Cache statistics**: total entries, hits, misses, stale count, hit rate percentage

### Phase 5: Multi-Level Verification Reporting

- **Four report levels**: Project (one-line), File (per-file), Symbol (per-function), Theorem (individual detail)
- **Debt visibility**: admitted/trusted counts always displayed prominently with `[N sorry]` / `[N assume]` markers
- **Error separation**: environment errors vs proof errors displayed in distinct sections
- **Machine-readable SDN output**: `render_sdn()` for tool integration
- **Source tracing**: failed theorems include source file path and line number
- **FileEntry / TheoremEntry**: structured report entries with formatting

### Phase 6: E2E Examples and Test Suite

- **Lean borrow verification**: `lean_borrow.spl` generates Lean 4 theorems from borrow checker analysis (borrow safety, no-aliasing, lifetime validity)
- **CLI test coverage**: `lean_verify_cli_spec.spl` tests `verify status`, `verify list`, `verify check`, `gen-lean verify`
- **Block integration tests**: `lean_block_integration_spec.spl` tests lean{} parsing, codegen integration, import dedup, collision detection
- **Workflow unit tests**: `lean_workflow_spec.spl` tests LeanCheckResult, VerificationSummary, proof obligations, regeneration inventory, strict checker
- **Regeneration models**: 15 verification domain models (nogc_compile, type_inference, memory_capabilities, memory_model_drf, tensor_dimensions, etc.)
- **18 verification subdirectories** in `verification/` with Lake projects

### Phase 7: Public Documentation

- **User guide**: `doc/07_guide/lean_verification_workflow.md` -- quick start, feature reference, commands, states, cache, reporting, limitations, examples
- **Completion report**: this document
- **Contract document**: `doc/04_architecture/lean_verification_contract.md` (created in Phase 0, referenced throughout)

## Files Created

### Core Verification Library (`src/compiler_rust/lib/std/src/verification/`)

| File | Purpose |
|------|---------|
| `state.spl` | VerificationState enum, aggregate_states, StateCounts |
| `proof_unit.spl` | ProofUnit model, ProofUnitSet collection |
| `fingerprint.spl` | Content fingerprinting for cache invalidation |
| `cache.spl` | Incremental verification cache with SDN storage |
| `report.spl` | Multi-level verification reporting (4 levels + SDN) |
| `toolchain.spl` | Lean/Lake detection, version validation, ToolchainError |
| `__init__.spl` | Module initialization |

### Lean Codegen (`src/compiler_rust/lib/std/src/verification/lean/`)

| File | Purpose |
|------|---------|
| `codegen.spl` | LeanCodegen pipeline, LeanTheorem, LeanCodegenOptions |
| `lean_block.spl` | LeanBlock model, theorem/import extraction, collision detection |
| `proof_ref.spl` | Proof reference resolution |
| `naming.spl` | Deterministic naming for generated Lean symbols |
| `runner.spl` | LeanCheckResult, VerificationSummary, Lean invocation |
| `emitter.spl` | Low-level Lean code emission |
| `contracts.spl` | Contract-to-Lean translation |
| `expressions.spl` | Expression translation |
| `expressions_eval.spl` | Expression evaluation for contracts |
| `functions.spl` | Function signature generation |
| `types.spl` | Type translation |
| `traits.spl` | Trait/impl translation |
| `structure_gen.spl` | Structure definition generation |
| `theorem_gen.spl` | Theorem statement generation |
| `beq_gen.spl` | BEq instance generation |
| `instantiation_gen.spl` | Generic instantiation |
| `lookup_gen.spl` | Lookup function generation |
| `memory_safety.spl` | Memory safety proof generation |
| `auto_gen.spl` | Automatic generation orchestration |
| `verification_checker.spl` | Verification constraint checking |
| `verification_diagnostics.spl` | Diagnostic messages |
| `__init__.spl` | Module initialization |

### Proof Infrastructure (`src/compiler_rust/lib/std/src/verification/proofs/`)

| File | Purpose |
|------|---------|
| `obligations.spl` | ProofObligation model, ProofStatus, contract extraction |
| `checker.spl` | ProofChecker for sorry/admit detection |
| `__init__.spl` | Module initialization |

### Verification Models (`src/compiler_rust/lib/std/src/verification/models/`)

15 domain model files: `async_compile`, `async_effects`, `contracts`, `gc_manual_borrow`, `memory_capabilities`, `memory_model_drf`, `module_resolution`, `nogc_compile`, `tensor_constraint`, `tensor_dim`, `tensor_dimensions`, `tensor_error`, `type_inference`, `visibility_export`, `__init__`

### Regeneration (`src/compiler_rust/lib/std/src/verification/regenerate/`)

12 regeneration modules: `async_compile`, `async_effect_inference`, `contracts`, `gc_manual_borrow`, `generics`, `macro_auto_import`, `manual_pointer_borrow`, `memory_capabilities`, `memory_model_drf`, `module_resolution`, `nogc_compile`, `tensor_dimensions`, `type_inference`, `visibility_export`, `__init__`

### Compiler Backend

| File | Purpose |
|------|---------|
| `src/compiler/70.backend/backend/lean_backend.spl` | LeanBackend, LeanBuilder, VerificationLevel, Codegen impl |
| `src/compiler/70.backend/backend/lean_mir_translate.spl` | MIR-to-Lean body/block/instruction translation |
| `src/compiler/70.backend/backend/lean_borrow.spl` | Borrow safety proof generation |
| `src/compiler/70.backend/backend/verification_codegen_types.spl` | VerificationCodegen trait |
| `src/compiler/70.backend/backend/common/verification_codegen.spl` | VerificationCodegen trait (re-export) |
| `src/compiler/35.semantics/verification_checker.spl` | VerificationChecker with V-* rules |

### Tests

| File | Purpose |
|------|---------|
| `test/system/compiler/lean_verify_cli_spec.spl` | CLI integration tests for verify/gen-lean commands |
| `test/system/compiler/lean_verification_workflow_spec.spl` | E2E workflow tests |
| `test/system/compiler/lean_auto_gen_spec.spl` | Auto-generation tests |
| `test/unit/compiler/verification/lean_basic_spec.spl` | Basic Lean generation tests |
| `test/unit/compiler/verification/lean_codegen_spec.spl` | Codegen pipeline tests |
| `test/unit/compiler/verification/lean_workflow_spec.spl` | Workflow unit tests (results, obligations, regeneration) |
| `test/unit/compiler/verification/lean_block_integration_spec.spl` | lean{} block integration tests |
| `test/unit/compiler/verification/verification_diagnostics_spec.spl` | Diagnostics tests |

### Documentation

| File | Purpose |
|------|---------|
| `doc/04_architecture/lean_verification_contract.md` | Authoritative contract (feature matrix, state model, commands) |
| `doc/07_guide/lean_verification_workflow.md` | User guide |
| `doc/09_report/lean_verification_complete_2026-04-04.md` | This completion report |

### Verification Projects (`verification/`)

18 Lake project directories: `async_compile`, `effect_system`, `gc_manual_borrow`, `gpu_types`, `macro_auto_import`, `manual_pointer_borrow`, `memory_capabilities`, `memory_model_drf`, `mixin_verification`, `module_resolution`, `monomorphization`, `nogc_compile`, `pattern_matching`, `static_dispatch_verification`, `tensor_dimensions`, `type_inference_compile`, `visibility_export`, `generated`

## Files Modified

| File | Change |
|------|--------|
| `src/compiler_rust/compiler/src/verification_checker.rs` | Rust-side verification checker (bootstrap) |
| `src/compiler_rust/compiler/src/codegen/lean/verification_checker.rs` | Rust-side Lean verification checker |
| `src/compiler_rust/compiler/src/codegen/lean/verification_diagnostics.rs` | Rust-side diagnostics |
| `src/compiler_rust/compiler/src/hir/types/verification.rs` | HIR verification type support |
| `src/i18n/strings_verification.spl` | Verification i18n strings |
| `src/i18n/verification.spl` | Verification i18n module |

## Scope Boundaries

### In Scope (Completed)

- Six-state verification model with aggregation rules
- Deterministic Lean 4 code generation from MIR
- Contract translation (in:/out:/out_err:/invariant:/decreases:/old())
- lean{} block integration with collision detection and import dedup
- External proof references via `proof uses:`
- Ghost function support with MIR erasure
- Trusted function support with debt tracking
- Lean/Lake toolchain validation with environment error separation
- Incremental verification cache with fingerprint-based invalidation
- Four-level verification reporting (project/file/symbol/theorem)
- Machine-readable SDN report format
- Borrow safety proof generation
- CLI commands: `gen-lean generate|write|compare|verify`, `verify status|check|list`
- User guide and contract documentation

### Out of Scope (Deferred)

| Feature | Reason |
|---------|--------|
| Loop invariants | Requires bounded loop analysis infrastructure |
| Refinement types | Separate gated subset, scope too broad for this milestone |
| Automatic proof synthesis | Research-grade capability, not productizable |
| Full dependent typing | Language-level change beyond verification |
| Replacing SSpec with proofs | Different concern (testing vs verification) |
| Symbol-level proof unit granularity | File-level is sufficient for v1; symbol-level is follow-on |

## Verification Evidence

```bash
# Check toolchain readiness
simple verify status

# Run verification CLI tests
simple test test/system/compiler/lean_verify_cli_spec.spl

# Run lean{} block integration tests
simple test test/unit/compiler/verification/lean_block_integration_spec.spl

# Run workflow unit tests
simple test test/unit/compiler/verification/lean_workflow_spec.spl

# Run basic and codegen tests
simple test test/unit/compiler/verification/lean_basic_spec.spl
simple test test/unit/compiler/verification/lean_codegen_spec.spl

# Generate and verify Lean output
simple gen-lean write
simple verify check

# List verification artifacts
simple verify list
```
