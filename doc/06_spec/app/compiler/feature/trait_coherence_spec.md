# Trait Coherence Specification

**Feature ID:** #TRAIT-COH-001 to #TRAIT-COH-017 | **Category:** Type System | Traits | **Status:** Implemented

_Source: `test/feature/usage/trait_coherence_spec.spl`_

---

## Coherence Rules

1. **Orphan Rule**: Either trait OR type must be local
2. **Overlap Rule**: No two impls for same trait+type
3. **Blanket Conflict**: Generic impl conflicts with specific
4. **Associated Types**: Same type must be declared consistently

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 20 |

## Test Structure

### Orphan Rule - Allowed Cases

- ✅ allows local trait on foreign type
- ✅ allows foreign trait on local type
- ✅ allows local trait on local type
### Orphan Rule - Rejection

- ✅ foreign trait on foreign type is rejected at compile time
### Overlap Detection - Same Type

- ✅ single impl is allowed
- ✅ duplicate impl is rejected at compile time
### Overlap Detection - Generic vs Concrete

- ✅ specific impl is allowed alone
- ✅ generic impl conflicts with specific
### No Overlap - Different Types

- ✅ different types can have same trait
### Associated Type Coherence

- ✅ associated type in impl is valid
- ✅ conflicting associated type is rejected
### Blanket Impl Conflict

- ✅ specific impl alone works
### Module Coherence Integration

- ✅ module with trait, struct, and impl passes
### Inherent Impl

- ✅ inherent impl on local type is allowed
### Multiple Traits Same Type

- ✅ multiple traits on same type
### Generic Type Impl

- ✅ impl on generic type
### Specialization with Default

- ✅ specialization placeholder
### Extension Trait Pattern

- ✅ extension trait on foreign type
- ✅ generic extension trait
### Negative Bounds Infrastructure

- ✅ impl with where clause

