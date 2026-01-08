# Mixin Implementation Plan with Lean Verification

**Date:** 2026-01-08  
**Status:** Planning & Specification Phase  
**Related Issues:** Type System Enhancement, Lean Verification

## Summary

This document outlines the implementation plan for strongly-typed mixins with formal verification via Lean 4.

## Completed Work

### Phase 0: Research & Specification ✅

1. **Research Document** (`doc/research/typed_mixins_research.md`)
   - Type system requirements
   - Type inference algorithm design
   - LL(1) compatible grammar
   - Lean verification strategy
   - Implementation phases

2. **BDD Feature Specifications** (Test-First Approach)
   - `specs/features/mixin_basic.feature` - 12 scenarios for basic mixins
   - `specs/features/mixin_generic.feature` - 14 scenarios for generic mixins
   - Covers: declaration, application, type inference, trait bounds, conflicts

3. **Example Code** (`examples/mixin_lean_verification.smp`)
   - Complete mixin examples
   - Generic mixins with type parameters
   - Trait requirements
   - Required methods
   - Contracts for verification

4. **Lean Verification Template** (`verification/type_inference_compile/src/MixinVerificationGenerated.lean`)
   - 10 theorems for mixin type safety
   - Generated structure definitions
   - Coherence and completeness proofs
   - Integration with existing Lean verification

## Implementation Phases

### Phase 1: Parser (Estimated: 2-3 days)

**Goal:** Parse mixin declarations and applications into AST

**Tasks:**
1. Add `Mixin` keyword to lexer (`src/parser/src/lexer/mod.rs`)
2. Add AST nodes:
   - `MixinDecl` in `src/parser/src/ast/nodes/definitions.rs`
   - `MixinRef` in `src/parser/src/ast/nodes/core.rs`
3. Implement parsing functions:
   - `parse_mixin_declaration()`
   - `parse_mixin_application()`
   - `parse_mixin_where_clause()`
4. Update `Declaration` enum to include `Mixin(MixinDecl)`

**Tests:** Run BDD specs from `specs/features/mixin_basic.feature` scenarios 1-3

**Acceptance Criteria:**
- [x] Can parse `mixin Name: ...` declarations
- [ ] Can parse `use MixinName` applications
- [ ] Can parse generic parameters `<T>`
- [ ] Can parse where clauses `where Self: Trait`

### Phase 2: Type System (Estimated: 4-5 days)

**Goal:** Type check mixins and infer type parameters

**Tasks:**
1. Add `MixinType` to type registry (`src/type/src/lib.rs`)
2. Implement mixin type inference (`src/type/src/inference.rs`)
3. Add constraint generation for generic mixins
4. Implement mixin application type checking:
   - Field type unification
   - Method signature matching
   - Trait requirement checking
   - Required method verification
5. Implement conflict detection (duplicate fields/methods)

**Tests:** Run BDD specs from both feature files

**Acceptance Criteria:**
- [ ] Mixin fields added to class type
- [ ] Type parameter `T` correctly inferred from usage
- [ ] Trait bounds validated at application
- [ ] Errors for missing required methods
- [ ] Errors for field name conflicts

### Phase 3: HIR Lowering ✅ (Completed: 2026-01-08)

**Goal:** Lower mixins to HIR and expand applications

**Tasks:**
1. ✅ Add HIR nodes for mixins (`src/compiler/src/hir/types/type_system.rs`)
   - Added `HirType::Mixin` variant with fields, methods, type params, trait bounds
   - Added `HirMixinMethod` structure for method signatures
2. ✅ Implement mixin lowering pass (`src/compiler/src/hir/lower/module_lowering.rs`)
   - Added `register_mixin()` method to register mixins in type registry
   - Integrated mixin registration in first pass of module lowering
3. ✅ Expand `use Mixin` into concrete field/method additions
   - Updated `register_class()` to apply mixin fields to classes
   - Added mixin method lowering in second pass for classes using mixins
4. ✅ Update pattern matches for Mixin variant
   - Added Lean code generation for mixins (`codegen/lean/types.rs`)
   - Added snapshot safety check for mixins (`hir/type_registry.rs`)
   - Fixed ClassDef initializers to include `mixins` field

**Implementation Details:**
- Mixin fields are added to class fields during `register_class()`
- Mixin methods are lowered and added to class methods in second pass
- Type parameters and trait bounds stored in HIR for future type checking
- Mixins compile to structure types in Lean verification

**Acceptance Criteria:**
- [x] Mixin type registered in HIR type system
- [x] Mixin fields added to classes that use them
- [x] Mixin methods lowered for classes
- [x] Lean code generation supports mixins
- [ ] Integration tests with compiled code (pending Phase 5)

**Next Steps:** Phase 4 - Complete Lean verification code generation

### Phase 4: Lean Code Generation (Estimated: 2-3 days)

**Goal:** Generate Lean verification code from Simple mixins

**Tasks:**
1. Extend `LeanType::Mixin` emission in `src/compiler/src/codegen/lean/types.rs`
2. Generate mixin structure definitions
3. Generate mixin application functions
4. Generate type soundness theorems:
   - Mixin application preserves types
   - Generic instantiation is sound
   - Required methods are complete
   - Multiple mixins are coherent
5. Add tests in `verification/type_inference_compile/`

**Tests:** Run Lean verification with `lake build`

**Acceptance Criteria:**
- [ ] `simple gen-lean` generates Lean code from mixin examples
- [ ] Generated Lean code type checks
- [ ] Theorems are stated (proof stubs OK)
- [ ] Integration with existing verification suite

### Phase 5: Testing & Documentation (Estimated: 2 days)

**Goal:** Comprehensive testing and documentation

**Tasks:**
1. Run all BDD feature specs (26 scenarios)
2. Add integration tests with real-world examples
3. Generate documentation from specs
4. Update language reference
5. Update CHANGELOG and FEATURES

**Acceptance Criteria:**
- [ ] All BDD scenarios pass
- [ ] Lean verification builds without errors
- [ ] Documentation generated from feature files
- [ ] Examples run successfully

## Test-Driven Development Approach

Following the principle "spec tests first, then implement":

1. **Write Specs First** ✅ - Feature files define expected behavior
2. **Red Phase** - Run tests (they should fail initially)
3. **Green Phase** - Implement minimal code to pass tests
4. **Refactor Phase** - Clean up implementation
5. **Verify Phase** - Run Lean proofs

## Verification Strategy

### Lean Properties to Verify

1. **Type Safety:** `mixin_application_preserves_type`
2. **Soundness:** `generic_instantiation_sound`  
3. **Completeness:** `required_methods_complete`
4. **Coherence:** `mixin_composition_no_duplicates`
5. **Substitution:** `type_param_substitution_consistent`

### Lean Verification Workflow

```bash
# 1. Write Simple code with mixins
vim examples/mixin_example.smp

# 2. Generate Lean verification code
./target/release/simple gen-lean generate

# 3. Build and check Lean proofs
cd verification/type_inference_compile
lake build

# 4. Compare with existing proofs
./target/release/simple gen-lean compare --diff
```

## Integration Points

### Existing Code to Modify

1. **Lexer:** `src/parser/src/lexer/mod.rs` - Add `Mixin` keyword
2. **Parser:** `src/parser/src/` - Mixin parsing
3. **AST:** `src/parser/src/ast/nodes/` - AST nodes
4. **Type System:** `src/type/src/` - Type checking
5. **HIR:** `src/compiler/src/hir/` - Lowering
6. **Lean Gen:** `src/compiler/src/codegen/lean/` - Verification

### Dependencies

- Existing type inference system (Hindley-Milner)
- Trait system for requirements
- Class/struct infrastructure
- Lean verification framework

## Success Metrics

- [ ] All 26 BDD scenarios pass
- [ ] Generated Lean code type checks
- [ ] 10+ theorems stated with axioms/sorry
- [ ] Zero regressions in existing tests
- [ ] Documentation generated from specs

## Timeline

- Phase 0: Research & Specs - **DONE** ✅
- Phase 1: Parser - 2-3 days
- Phase 2: Type System - 4-5 days
- Phase 3: HIR Lowering - 2-3 days
- Phase 4: Lean Generation - 2-3 days
- Phase 5: Testing & Docs - 2 days

**Total Estimated:** 12-16 days

## Next Steps

1. ✅ Create research document
2. ✅ Write BDD feature specs
3. ✅ Create example code
4. ✅ Create Lean verification template
5. ⏭️ **Start Phase 1:** Add `Mixin` keyword to lexer
6. ⏭️ Implement `parse_mixin_declaration()`
7. ⏭️ Run first BDD test (should fail - RED)
8. ⏭️ Implement parser to pass test (GREEN)

## References

- `doc/research/typed_mixins_research.md` - Detailed research
- `specs/features/mixin_*.feature` - BDD specifications
- `verification/type_inference_compile/src/Mixins.lean` - Existing verification
- `AGENTS.md` - Development guidelines

---

**Note:** This is a living document. Update as implementation progresses.
