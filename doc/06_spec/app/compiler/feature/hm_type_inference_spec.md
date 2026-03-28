# Hindley-Milner Type Inference

**Feature ID:** #TYPE-001 | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/usage/hm_type_inference_spec.spl`_

---

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
val result = unify(empty_subst(), v, ty_int())
val free_vars = collect_free_vars(fn_ty, 0)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 15 |

## Test Structure

### HM Type Inference Core

#### Fresh Type Variables

- ✅ creates unique type variable IDs
- ✅ creates type variables with levels
#### Unification

- ✅ unifies same primitive types
- ✅ fails to unify different primitive types
- ✅ unifies type variable with concrete type
- ✅ unifies two type variables
- ✅ detects occurs check violation
- ✅ unifies function types
- ✅ unifies function types with variables
#### Level-Based Generalization

- ✅ identifies variables at higher level as generalizable
- ✅ does not generalize variables at same level
- ✅ generalizes only higher-level vars in mixed type
#### Let-Polymorphism Concept

- ✅ demonstrates identity can be used at multiple types
#### Algorithm W Core Steps

- ✅ infers identity function type
- ✅ infers application type

