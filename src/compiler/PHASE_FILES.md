# Phase Files - Development Evolution Documentation

**Purpose:** These files represent the incremental development history of complex compiler features.

---

## What Are Phase Files?

Phase files (e.g., `bidir_phase1a.spl`, `variance_phase6c.spl`) document the step-by-step implementation of advanced type system features. Each phase represents a milestone in development:

- **Phase A:** Foundation (types, enums, basic structures)
- **Phase B:** Core logic implementation
- **Phase C:** Integration with existing compiler
- **Phase D:** Optimization and edge cases

---

## Current Phase Files (27 files, ~12K lines)

### Bidirectional Type Checking (Phase 1)
- `bidir_phase1a.spl` - InferMode parameter
- `bidir_phase1b.spl` - Application & let binding
- `bidir_phase1c.spl` - Pattern matching
- `bidir_phase1d.spl` - Subsumption rules

**Total:** 4 files, ~1,800 lines

### Associated Types (Phase 4)
- `associated_types_phase4a.spl` - Type projection
- `associated_types_phase4b.spl` - Trait constraints
- `associated_types_phase4c.spl` - Normalization
- `associated_types_phase4d.spl` - Caching

**Total:** 4 files, ~2,100 lines

### Higher-Rank Polymorphism (Phase 5)
- `higher_rank_poly_phase5a.spl` - Rank-N types
- `higher_rank_poly_phase5b.spl` - Skolemization
- `higher_rank_poly_phase5c.spl` - Unification
- `higher_rank_poly_phase5d.spl` - Impredicative polymorphism

**Total:** 4 files, ~2,300 lines

### Variance Checking (Phase 6)
- `variance_phase6a.spl` - Variance annotations
- `variance_phase6b.spl` - Inference algorithm
- `variance_phase6c.spl` - Subtyping rules
- `variance_phase6d.spl` - Integration with generics

**Total:** 4 files, ~1,900 lines

### Macro Hygiene (Phase 7)
- `macro_checker_phase7a.spl` - Hygiene basics
- `macro_checker_phase7b.spl` - Scope tracking
- `macro_checker_phase7c.spl` - Template expansion

**Total:** 3 files, ~1,500 lines

### Const Generics (Phase 8)
- `const_keys_phase8a.spl` - Const parameters
- `const_keys_phase8b.spl` - Const evaluation
- `const_keys_phase8c.spl` - Type system integration

**Total:** 3 files, ~1,200 lines

### SIMD Intrinsics (Phase 9)
- `simd_phase9a.spl` - Vector types
- `simd_phase9b.spl` - Operations
- `simd_phase9c.spl` - Backend lowering

**Total:** 3 files, ~1,200 lines

---

## Why Phase Files Exist

1. **Educational Value** - Shows how complex features are built incrementally
2. **Development History** - Preserves the evolution of the type system
3. **Debugging Reference** - Helps understand why certain design decisions were made
4. **Testing Isolation** - Each phase can be tested independently

---

## Duplication in Phase Files

Phase files DO contain some duplication:
- Type definitions redefined across phases (e.g., `InferMode`, `HirType`)
- Helper functions repeated with slight variations
- Similar error handling patterns

**This is intentional** - each phase is meant to be somewhat self-contained for development purposes.

---

## Should Phase Files Be Consolidated?

### Arguments For Consolidation
- Reduces ~8K lines of duplication
- Simpler codebase structure
- Easier maintenance (single source of truth)

### Arguments Against Consolidation
- Loses development history
- Makes it harder to understand feature evolution
- Some phases may not be fully integrated yet
- Testing might rely on phase boundaries

### Current Decision: **Keep As-Is**

The phase files are kept for their educational and historical value. If you're working on one of these features, refer to the highest phase number (e.g., `bidir_phase1d.spl` for bidirectional checking).

---

## Working with Phase Files

### If You're Reading Code
- **Start with Phase D** (or highest phase) - this is the most complete implementation
- Use earlier phases to understand the progression
- Check git history for when each phase was added

### If You're Modifying a Feature
- **Update the highest phase** (e.g., `variance_phase6d.spl`)
- Consider whether earlier phases need updates for consistency
- Add comments explaining which phase is "production"

### If You're Adding a New Feature
- You can create phase files if the feature is complex
- Follow the naming convention: `feature_phase{N}{a-d}.spl`
- Each phase should compile and pass tests independently

---

## Future Consolidation Plan

If phase files are consolidated in the future:

1. **Archive to `doc/design/phases/`**
   - Preserve historical value
   - Move out of production source tree

2. **Create consolidated files**
   - `bidirectional_checking.spl` (merge phase1a-d)
   - `associated_types.spl` (merge phase4a-d)
   - etc.

3. **Update imports and tests**
   - Replace phase imports with consolidated imports
   - Ensure all tests pass

**Estimated effort:** 2-3 days, medium risk

---

## Related Documentation

- `DESUGARING_PLAN.md` - How Full Simple → Core Simple transformation works
- `src/compiler/README.md` - Compiler architecture overview
- `src/compiler/README.md` - Current bootstrap and consolidation status

---

## Status

- **Created:** 2026-02-11
- **Status:** Phase files are part of production codebase
- **Consolidation:** Deferred (low priority)
- **Duplication:** ~12K lines (documented, intentional for development)
