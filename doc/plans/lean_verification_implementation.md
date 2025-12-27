# Lean Verification Mode — Implementation Plan

**Version:** 2025-12-29
**Status:** Complete (Phase 6 Complete - 100%)
**Specification:** [lean_verification_with_aop.md](../research/lean_verification_with_aop.md)

---

## Overview

This plan outlines the implementation of Simple's Lean verification mode, which generates Lean 4 artifacts from verified Simple code and enforces strict constraints on AOP and macros to ensure soundness.

---

## Implementation Progress

| Phase | Description | Status | Files |
|-------|-------------|--------|-------|
| 1.1 | Verification Context Infrastructure | ✅ Complete | `src/compiler/src/hir/types/` |
| 1.2 | Contract Clause Parsing | ✅ Complete | `src/parser/src/statements/` |
| 1.3 | Verified Subset Enforcement | ✅ Complete | `src/compiler/src/hir/` |
| 2.1 | AOP Constraint Enforcement | ✅ Complete | `src/compiler/src/aop/` |
| 2.2 | Ghost Aspect Validation | ✅ Complete | `src/compiler/src/aop/` |
| 3.1 | Macro Introduction Contracts | ✅ Complete | `src/compiler/src/interpreter_macro/` |
| 3.2 | Verified Context Macro Restrictions | ✅ Complete | `src/compiler/src/interpreter_macro/` |
| 4.1 | Lean Backend Infrastructure | ✅ Complete | `src/compiler/src/codegen/lean/` |
| 4.2 | Contract Translation | ✅ Complete | `src/compiler/src/codegen/lean/contracts.rs` |
| 4.3 | Function Translation | ✅ Complete | `src/compiler/src/codegen/lean/functions.rs` |
| 5.1 | Diagnostics | ✅ Complete | `src/compiler/src/codegen/lean/verification_diagnostics.rs` |
| 5.2 | Build Integration | ✅ Complete | `src/pkg/src/manifest.rs`, `src/compiler/src/codegen/lean/runner.rs` |
| 5.3 | LSP Integration | ✅ Complete | `simple/app/lsp/handlers/verification.spl` |
| 6.1 | Verification Models in Simple | ✅ Complete | `simple/std_lib/src/verification/models/` |
| 6.2 | Lean Code Generator in Simple | ✅ Complete | `simple/std_lib/src/verification/lean/` |
| 6.3 | Regeneration & Validation | ✅ Complete | `simple/app/verify/main.spl` |
| 6.4 | Proof Obligation Management | ✅ Complete | `simple/std_lib/src/verification/proofs/` |

### Implementation Notes (Phase 5.2)

**Files Created:**
- `src/compiler/src/codegen/lean/verification_diagnostics.rs` - 24 verification error codes (V-AOP-*, M-INTRO-*, V-MACRO-*, V-TERM-*, V-UNSAFE-*, V-DEP-*, V-INHERIT-*, V-EFFECT-*, V-GHOST-*, V-CONTRACT-*)
- `src/compiler/src/codegen/lean/verification_checker.rs` - HIR verification constraint checker
- `src/compiler/src/codegen/lean/runner.rs` - Lean invocation and proof checking

**Files Modified:**
- `src/pkg/src/manifest.rs` - Added `VerifyConfig` struct for `[verify]` section in simple.toml
- `src/compiler/src/codegen/lean/mod.rs` - Module exports for verification_diagnostics, verification_checker, runner

### Implementation Notes (Phase 5.3 - LSP Integration)

**Files Created:**
- `simple/app/lsp/handlers/verification.spl` - Verification status handler with:
  - `VerificationStatus` enum (Verified, Trusted, Partial, Failed, NotVerified)
  - `VerificationDiagnostic` class with LSP diagnostic conversion
  - `VerifiedSymbol` class for tracking verified symbols
  - `handle_verification_diagnostics()` - Generate verification diagnostics
  - `handle_verification_hover()` - Hover info for verified symbols
  - `handle_lean_definition()` - Go-to-definition for Lean artifacts
  - `get_verification_symbols()` - Document symbols with verification status

**Files Modified:**
- `simple/app/lsp/handlers/diagnostics.spl` - Added verification diagnostics integration
- `simple/app/lsp/handlers/hover.spl` - Added verification hover info
- `simple/app/lsp/handlers/definition.spl` - Added Lean artifact navigation
- `simple/app/lsp/server.spl` - Added handlers for `simple/leanDefinition` and `simple/verificationSymbols`

### Implementation Notes (Phase 6 - Self-Hosting Complete)

**Phase 6.1 - Verification Models in Simple:**
- `simple/std_lib/src/verification/__init__.spl` - Main module exports
- `simple/std_lib/src/verification/models/__init__.spl` - Model exports
- `simple/std_lib/src/verification/models/memory_capabilities.spl` - RefCapability enum, CapType, Reference, RefEnv classes
- `simple/std_lib/src/verification/models/contracts.spl` - ContractExprKind enum, ContractExpr, FunctionContract classes
- `simple/std_lib/src/verification/models/memory_model_drf.spl` - SC-DRF model with MemoryOrder, ThreadState, RaceDetector
- `simple/std_lib/src/verification/models/type_inference.spl` - Hindley-Milner inference with Type enum, InferenceContext
- `simple/std_lib/src/verification/models/async_effects.spl` - Effect tracking with EffectKind, AsyncEffectChecker

**Phase 6.2 - Lean Code Generator in Simple:**
- `simple/std_lib/src/verification/lean/__init__.spl` - Lean module exports
- `simple/std_lib/src/verification/lean/codegen.spl` - LeanCodegen, LeanFunction, LeanTheorem, LeanStructure, LeanInductive
- `simple/std_lib/src/verification/lean/emitter.spl` - LeanEmitter class with emit_* methods
- `simple/std_lib/src/verification/lean/types.spl` - Type translation (SimpleType, ClassDef, EnumDef, FunctionDef)
- `simple/std_lib/src/verification/lean/expressions.spl` - Expression translation with translate_contract_expr()

**Phase 6.3 - Regeneration & Validation:**
- `simple/app/verify/main.spl` - CLI tool with regenerate, check, status, list commands
- `simple/app/verify/__init__.spl` - Package exports

**Phase 6.4 - Proof Obligation Management:**
- `simple/std_lib/src/verification/proofs/__init__.spl` - Proofs module exports
- `simple/std_lib/src/verification/proofs/obligations.spl` - ProofObligation, ObligationSet, extract_from_contract()
- `simple/std_lib/src/verification/proofs/checker.spl` - ProofChecker, LeanResult, CheckerConfig, BatchCheckResult

---

## Phase 1: Foundation (Milestone 1)

### 1.1 Verification Context Infrastructure

**Objective:** Implement `@verify`, `@trusted`, `@unsafe`, and `ghost` attributes.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| Parse `@verify` attribute | Parser | `src/parser/src/statements/` | 2 |
| Parse `@trusted` attribute | Parser | `src/parser/src/statements/` | 2 |
| Parse `@unsafe` attribute | Parser | `src/parser/src/statements/` | 2 |
| Parse `ghost` modifier | Parser | `src/parser/src/statements/` | 2 |
| Add verification context to HIR | HIR | `src/compiler/src/hir/` | 3 |
| Propagate verification context (V-SCOPE) | HIR | `src/compiler/src/hir/lower/` | 3 |
| Enforce V-INHERIT rule | HIR | `src/compiler/src/hir/lower/` | 3 |
| Implement V-DEP dependency checking | HIR | `src/compiler/src/hir/` | 3 |

### 1.2 Contract Clause Parsing

**Objective:** Parse `requires:`, `ensures:`, `invariant:`, `decreases:`, `modifies:`.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| Parse `requires:` clause | Parser | `src/parser/src/statements/` | 2 |
| Parse `ensures:` with `result` binding | Parser | `src/parser/src/statements/` | 2 |
| Parse `invariant:` on classes | Parser | `src/parser/src/statements/` | 2 |
| Parse `decreases:` clause | Parser | `src/parser/src/statements/` | 2 |
| Parse `modifies:` clause (optional) | Parser | `src/parser/src/statements/` | 2 |
| Add contract clauses to AST | AST | `src/parser/src/ast/` | 2 |

### 1.3 Verified Subset Enforcement

**Objective:** Implement compile-time restrictions for Lean-checked code.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| V-UNSAFE: Detect unsafe primitives | HIR | `src/compiler/src/hir/` | 3 |
| V-PARTIAL: Reject unproven recursion | HIR | `src/compiler/src/hir/` | 4 |
| V-EFFECT: Block IO/FFI in verified code | HIR | `src/compiler/src/hir/` | 3 |
| V-REFLECT: Block reflection | HIR | `src/compiler/src/hir/` | 2 |
| V-TERM: Require termination arguments | HIR | `src/compiler/src/hir/` | 4 |

---

## Phase 2: AOP Integration

### 2.1 AOP Constraint Enforcement

**Objective:** Ensure only ghost aspects can target verified join points.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| Track verified join points | AOP | `src/compiler/src/aop/` | 3 |
| V-AOP-GHOST: Enforce ghost-only aspects | AOP | `src/compiler/src/aop/` | 3 |
| V-AOP-EXPLICIT: Require explicit pointcuts | AOP | `src/compiler/src/aop/` | 2 |
| V-AOP-ADVICE: Restrict around advice | AOP | `src/compiler/src/aop/` | 3 |
| V-AOP-INTRO: Block runtime introductions | AOP | `src/compiler/src/aop/` | 3 |

### 2.2 Ghost Aspect Validation

**Objective:** Validate ghost aspects only touch ghost state.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| Ghost state tracking | HIR | `src/compiler/src/hir/` | 3 |
| Validate before/after only use ghost | AOP | `src/compiler/src/aop/` | 3 |
| Validate around calls proceed once | AOP | `src/compiler/src/aop/` | 3 |

---

## Phase 3: Macro Integration

### 3.1 Macro Introduction Contracts

**Objective:** Enforce `introduces:` contracts on macros.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| Parse `introduces:` clause | Parser | `src/parser/src/statements/macro_parsing.rs` | 3 |
| Track macro-introduced symbols | Macro | `src/compiler/src/interpreter_macro/` | 4 |
| M-INTRO-EXACT: Verify declarations match | Macro | `src/compiler/src/interpreter_macro/` | 4 |

### 3.2 Verified Context Macro Restrictions

**Objective:** Enforce restrictions on macros in verified contexts.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| V-MACRO-NO-PUB: Block public introductions | Macro | `src/compiler/src/interpreter_macro/` | 3 |
| V-MACRO-NO-GLOBAL: Block global introductions | Macro | `src/compiler/src/interpreter_macro/` | 3 |
| V-MACRO-GHOST-ONLY: Require ghost-only | Macro | `src/compiler/src/interpreter_macro/` | 3 |
| V-MACRO-AOP: Restrict generated aspects | Macro | `src/compiler/src/interpreter_macro/` | 3 |

---

## Phase 4: Lean Code Generation

### 4.1 Lean Backend Infrastructure

**Objective:** Create Lean 4 code generation backend.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| Lean backend module structure | Codegen | `src/compiler/src/codegen/lean/` | 3 |
| Type translation (class → structure) | Codegen | `src/compiler/src/codegen/lean/types.rs` | 4 |
| Enum translation (enum → inductive) | Codegen | `src/compiler/src/codegen/lean/types.rs` | 4 |
| Sum type translation | Codegen | `src/compiler/src/codegen/lean/types.rs` | 3 |

### 4.2 Contract Translation

**Objective:** Translate contracts to Lean propositions and theorems.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| Invariant → `def inv : T → Prop` | Codegen | `src/compiler/src/codegen/lean/contracts.rs` | 4 |
| requires/ensures → theorem statements | Codegen | `src/compiler/src/codegen/lean/contracts.rs` | 4 |
| decreases → termination arguments | Codegen | `src/compiler/src/codegen/lean/contracts.rs` | 5 |
| Generate proof obligation stubs | Codegen | `src/compiler/src/codegen/lean/proofs.rs` | 4 |

### 4.3 Function Translation

**Objective:** Translate verified functions to Lean.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| Basic function translation | Codegen | `src/compiler/src/codegen/lean/functions.rs` | 4 |
| Expression translation | Codegen | `src/compiler/src/codegen/lean/expressions.rs` | 4 |
| Pattern matching translation | Codegen | `src/compiler/src/codegen/lean/patterns.rs` | 4 |
| Ghost erasure | Codegen | `src/compiler/src/codegen/lean/ghost.rs` | 3 |

---

## Phase 5: Tooling & Integration

### 5.1 Diagnostics

**Objective:** Implement all required error codes.

| Error Code | Description | Priority |
|------------|-------------|----------|
| V-AOP-001 | Non-ghost aspect targets verified join point | High |
| V-AOP-002 | Verified pointcut uses wildcard | Medium |
| V-AOP-003 | Aspect introduces runtime member | High |
| M-INTRO-001 | Undeclared macro introduction | High |
| V-MACRO-001 | Macro introduces pub in verified | High |
| V-MACRO-002 | Macro introduces global in verified | High |
| V-MACRO-003 | Macro introduces runtime in verified | High |
| V-TERM-001 | Missing termination argument | High |
| V-UNSAFE-001 | Unsafe primitive in verified | High |
| V-DEP-001 | Missing @trusted boundary | High |
| V-INHERIT-001 | Opt-out from verified inheritance | High |

### 5.2 Build Integration

**Objective:** Integrate Lean verification into build pipeline.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| `simple.toml` verify config | Driver | `src/driver/` | 2 |
| `__init__.spl` package verify | Parser | `src/parser/` | 2 |
| Lean artifact output directory | Codegen | `src/compiler/src/codegen/lean/` | 2 |
| Invoke Lean for proof checking | Driver | `src/driver/` | 3 |

### 5.3 LSP Integration

**Objective:** Show verification status in IDE.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| Verification status diagnostics | LSP | `simple/app/lsp/` | 3 |
| Hover info for verified symbols | LSP | `simple/app/lsp/` | 2 |
| Go-to-definition for Lean artifacts | LSP | `simple/app/lsp/` | 3 |

---

## Phase 6: Self-Hosting (Simple-Based Lean Generation)

### 6.1 Verification Models in Simple

**Objective:** Port verification models from Lean to Simple with Rust-compatible interface.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| Create verification module structure | Stdlib | `simple/std_lib/src/verification/` | 2 |
| Port RefCapability enum | Models | `verification/models/memory_capabilities.spl` | 2 |
| Port CapType, Reference, RefEnv | Models | `verification/models/memory_capabilities.spl` | 3 |
| Port canCreateRef, canConvert | Models | `verification/models/memory_capabilities.spl` | 3 |
| Port ContractExpr enum | Models | `verification/models/contracts.spl` | 3 |
| Port FunctionContract | Models | `verification/models/contracts.spl` | 3 |
| Port contract checking functions | Models | `verification/models/contracts.spl` | 3 |
| Port SC-DRF model | Models | `verification/models/memory_model_drf.spl` | 4 |
| Port type inference model | Models | `verification/models/type_inference.spl` | 4 |
| Port async/effect model | Models | `verification/models/async_compile.spl` | 3 |

### 6.2 Lean Code Generator in Simple

**Objective:** Implement Lean syntax emission in Simple.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| LeanCodegen class | Lean | `verification/lean/codegen.spl` | 3 |
| emit_structure() for classes | Lean | `verification/lean/types.spl` | 3 |
| emit_inductive() for enums | Lean | `verification/lean/types.spl` | 3 |
| emit_def() for functions | Lean | `verification/lean/types.spl` | 3 |
| emit_theorem() for contracts | Lean | `verification/lean/contracts.spl` | 4 |
| emit_prop() for invariants | Lean | `verification/lean/contracts.spl` | 3 |
| Expression translation | Lean | `verification/lean/expressions.spl` | 4 |
| Lean syntax emitter | Lean | `verification/lean/emitter.spl` | 3 |

### 6.3 Regeneration & Validation

**Objective:** Regenerate existing Lean files and validate output.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| regenerate_memory_capabilities() | Regen | `verification/regenerate.spl` | 3 |
| regenerate_contracts() | Regen | `verification/regenerate.spl` | 3 |
| regenerate_memory_model_drf() | Regen | `verification/regenerate.spl` | 3 |
| regenerate_type_inference() | Regen | `verification/regenerate.spl` | 3 |
| regenerate_all() orchestrator | Regen | `verification/regenerate.spl` | 2 |
| Lean regeneration test suite | Test | `test/unit/verification/lean_regen_spec.spl` | 3 |
| CI validation job | CI | `.github/workflows/` | 2 |

### 6.4 Proof Obligation Management

**Objective:** Generate and track proof obligations.

| Task | Component | Files | Est. Difficulty |
|------|-----------|-------|-----------------|
| ProofObligation class | Proofs | `verification/proofs/obligations.spl` | 3 |
| Extract obligations from contracts | Proofs | `verification/proofs/obligations.spl` | 4 |
| Generate theorem stubs | Proofs | `verification/proofs/obligations.spl` | 3 |
| Lean invocation wrapper | Proofs | `verification/proofs/checker.spl` | 3 |
| Proof status tracking | Proofs | `verification/proofs/checker.spl` | 3 |

---

## Feature Summary (Updated)

### Feature IDs: #1840-#1919 (Lean Verification Mode + Self-Hosting)

| ID | Feature | Difficulty | Phase |
|----|---------|------------|-------|
| #1840 | `@verify` attribute | 2 | 1.1 |
| #1841 | `@trusted` attribute | 2 | 1.1 |
| #1842 | `@unsafe` attribute | 2 | 1.1 |
| #1843 | `ghost` modifier | 2 | 1.1 |
| #1844 | V-SCOPE propagation | 3 | 1.1 |
| #1845 | V-INHERIT enforcement | 3 | 1.1 |
| #1846 | V-DEP dependency checking | 3 | 1.1 |
| #1847 | `requires:` clause | 2 | 1.2 |
| #1848 | `ensures:` clause | 2 | 1.2 |
| #1849 | `invariant:` clause | 2 | 1.2 |
| #1850 | `decreases:` clause | 2 | 1.2 |
| #1851 | V-UNSAFE enforcement | 3 | 1.3 |
| #1852 | V-PARTIAL enforcement | 4 | 1.3 |
| #1853 | V-EFFECT enforcement | 3 | 1.3 |
| #1854 | V-TERM enforcement | 4 | 1.3 |
| #1855 | V-AOP-GHOST rule | 3 | 2.1 |
| #1856 | V-AOP-EXPLICIT rule | 2 | 2.1 |
| #1857 | V-AOP-ADVICE rule | 3 | 2.1 |
| #1858 | V-AOP-INTRO rule | 3 | 2.1 |
| #1859 | Ghost state tracking | 3 | 2.2 |
| #1860 | `introduces:` clause | 3 | 3.1 |
| #1861 | M-INTRO-EXACT rule | 4 | 3.1 |
| #1862 | V-MACRO-NO-PUB rule | 3 | 3.2 |
| #1863 | V-MACRO-NO-GLOBAL rule | 3 | 3.2 |
| #1864 | V-MACRO-GHOST-ONLY rule | 3 | 3.2 |
| #1865 | V-MACRO-AOP rule | 3 | 3.2 |
| #1866 | Lean type translation | 4 | 4.1 |
| #1867 | Lean enum translation | 4 | 4.1 |
| #1868 | Contract → Prop translation | 4 | 4.2 |
| #1869 | Theorem stub generation | 4 | 4.2 |
| #1870 | Termination argument gen | 5 | 4.2 |
| #1871 | Function translation | 4 | 4.3 |
| #1872 | Expression translation | 4 | 4.3 |
| #1873 | Pattern translation | 4 | 4.3 |
| #1874 | Ghost erasure | 3 | 4.3 |
| #1875 | Verification diagnostics (11 codes) | 3 | 5.1 |
| #1876 | Build config integration | 2 | 5.2 |
| #1877 | Lean invocation | 3 | 5.2 |
| #1878 | LSP verification status | 3 | 5.3 |
| #1879 | LSP Lean artifact navigation | 3 | 5.3 |
| #1880 | Verification module structure (Simple) | 2 | 6.1 |
| #1881 | RefCapability model (Simple) | 2 | 6.1 |
| #1882 | CapType/Reference/RefEnv (Simple) | 3 | 6.1 |
| #1883 | canCreateRef/canConvert (Simple) | 3 | 6.1 |
| #1884 | ContractExpr model (Simple) | 3 | 6.1 |
| #1885 | FunctionContract model (Simple) | 3 | 6.1 |
| #1886 | Contract checking (Simple) | 3 | 6.1 |
| #1887 | SC-DRF model (Simple) | 4 | 6.1 |
| #1888 | Type inference model (Simple) | 4 | 6.1 |
| #1889 | Async/effect model (Simple) | 3 | 6.1 |
| #1890 | LeanCodegen class (Simple) | 3 | 6.2 |
| #1891 | emit_structure() (Simple) | 3 | 6.2 |
| #1892 | emit_inductive() (Simple) | 3 | 6.2 |
| #1893 | emit_def() (Simple) | 3 | 6.2 |
| #1894 | emit_theorem() (Simple) | 4 | 6.2 |
| #1895 | emit_prop() (Simple) | 3 | 6.2 |
| #1896 | Expression translation (Simple) | 4 | 6.2 |
| #1897 | Lean syntax emitter (Simple) | 3 | 6.2 |
| #1898 | regenerate_memory_capabilities() | 3 | 6.3 |
| #1899 | regenerate_contracts() | 3 | 6.3 |
| #1900 | regenerate_memory_model_drf() | 3 | 6.3 |
| #1901 | regenerate_type_inference() | 3 | 6.3 |
| #1902 | regenerate_all() orchestrator | 2 | 6.3 |
| #1903 | Lean regeneration test suite | 3 | 6.3 |
| #1904 | CI validation job | 2 | 6.3 |
| #1905 | ProofObligation class | 3 | 6.4 |
| #1906 | Extract obligations from contracts | 4 | 6.4 |
| #1907 | Generate theorem stubs | 3 | 6.4 |
| #1908 | Lean invocation wrapper (Simple) | 3 | 6.4 |
| #1909 | Proof status tracking | 3 | 6.4 |

**Total:** 70 features (40 core + 30 self-hosting)

---

## Dependencies

### External
- Lean 4 toolchain (for proof checking)
- Lean 4 standard library

### Internal
- AOP system (complete)
- Macro system (complete)
- Contract system (complete)
- HIR infrastructure (complete)
- File I/O (complete)
- String manipulation (complete)

---

## Testing Strategy

### Unit Tests
- Attribute parsing tests
- Contract clause parsing tests
- Verification context propagation tests
- Constraint violation detection tests

### Integration Tests
- End-to-end verified module compilation
- Lean artifact validation
- AOP + verification interaction tests
- Macro + verification interaction tests

### System Tests
- Lean proof checking integration
- Build pipeline with verification
- LSP verification status display

---

## Related Documentation

- [Lean Verification Specification](../research/lean_verification_with_aop.md)
- [AOP Specification](../research/aop.md)
- [Macro Contracts](../contracts/macro_contracts.md)
- [Memory Model Verification](../architecture/memory_model_implementation.md)
