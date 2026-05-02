# Trait Coherence Specification

Tests trait coherence rules including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TRAIT-COH-001 to #TRAIT-COH-017 |
| Category | Type System \| Traits |
| Status | Implemented |
| Source | `test/feature/usage/trait_coherence_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests trait coherence rules including:
- Orphan rule enforcement
- Overlap detection
- Blanket impl conflicts
- Associated type coherence
- Specialization with @default

## Coherence Rules

1. **Orphan Rule**: Either trait OR type must be local
2. **Overlap Rule**: No two impls for same trait+type
3. **Blanket Conflict**: Generic impl conflicts with specific
4. **Associated Types**: Same type must be declared consistently

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/trait_coherence/result.json` |

## Scenarios

- allows local trait on foreign type
- allows foreign trait on local type
- allows local trait on local type
- foreign trait on foreign type is rejected at compile time
- single impl is allowed
- duplicate impl is rejected at compile time
- specific impl is allowed alone
- generic impl conflicts with specific
- different types can have same trait
- associated type in impl is valid
- conflicting associated type is rejected
- specific impl alone works
- module with trait, struct, and impl passes
- inherent impl on local type is allowed
- multiple traits on same type
- impl on generic type
- specialization placeholder
- extension trait on foreign type
- generic extension trait
- impl with where clause
