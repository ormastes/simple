# Hindley-Milner Type Inference

Tests core Hindley-Milner type inference with level-based generalization. Implements simplified type variables, substitution, and unification with occurs check to verify polymorphic functions, let-polymorphism with independent instantiations, function type unification, and Algorithm W core steps for identity and application type inference.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TYPE-001 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/feature/usage/hm_type_inference_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests core Hindley-Milner type inference with level-based generalization.
Implements simplified type variables, substitution, and unification with occurs
check to verify polymorphic functions, let-polymorphism with independent
instantiations, function type unification, and Algorithm W core steps for
identity and application type inference.

## Syntax

```simple
val v = ty_var(0)
val fn_ty = ty_fn(v, v)  # a -> a
var result = unify(empty_subst(), v, ty_int())
val free_vars = collect_free_vars(fn_ty, 0)
```
HM Type Inference Specification

Tests for Hindley-Milner type inference with level-based generalization.
Verifies that the type inference correctly handles:
- Polymorphic functions (identity, compose)
- Let-polymorphism (multiple instantiations)
- Unification with occurs check
- Level-based generalization

Feature: #2500 - HM Type Inference
Status: in_progress

NOTE: Full tests require self-hosting compiler modules (simple/compiler/*).
      These simplified tests verify core concepts using built-in primitives.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/hm_type_inference/result.json` |

## Scenarios

- creates unique type variable IDs
- creates type variables with levels
- unifies same primitive types
- fails to unify different primitive types
- unifies type variable with concrete type
- unifies two type variables
- detects occurs check violation
- unifies function types
- unifies function types with variables
- identifies variables at higher level as generalizable
- does not generalize variables at same level
- generalizes only higher-level vars in mixed type
- demonstrates identity can be used at multiple types
- infers identity function type
- infers application type
