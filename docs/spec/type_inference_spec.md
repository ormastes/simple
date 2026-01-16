# Type Inference & Unification

*Source: `simple/std_lib/test/features/infrastructure/type_inference_spec.spl`*

---

# Type Inference & Unification

**Feature ID:** #100
**Category:** Infrastructure - Type System
**Difficulty:** 5/5
**Status:** Complete

## Overview

The Type Inference system implements Hindley-Milner type inference with Lean 4 verification,
providing automatic type deduction for expressions without requiring type annotations.

## Key Features

- **Literal Type Inference:** Automatic inference of integer, float, string, boolean types
- **Generic Instantiation:** Type parameter resolution from usage context
- **Unification Algorithm:** Robinson's algorithm with occurs-check
- **Lean Verification:** Formal proofs of determinism and soundness
- **Pattern Matching:** Exhaustiveness checking with type refinement

## Implementation

**Primary Files:**
- `src/type/src/lib.rs` - Type system entry point, Lean model bridge
- `src/type/src/checker_infer.rs` - Hindley-Milner inference algorithm
- `src/type/src/checker_unify.rs` - Robinson unification

**Verification:**
- `verification/type_inference_compile/` - Lean 4 formal proofs

**Dependencies:**
- Feature #2: Parser
- Feature #3: AST

**Required By:**
- Feature #4: HIR
- Feature #101: Effect System

**Given** integer literal
        **When** type inference runs
        **Then** infers i64

        **Verification:** Integer inference works

**Given** float literal
        **When** type inference runs
        **Then** infers f64

        **Verification:** Float inference works

**Given** string literal
        **When** type inference runs
        **Then** infers string

        **Verification:** String inference works

**Given** generic function usage
        **When** type inference runs
        **Then** instantiates type parameters

        **Verification:** Generic instantiation works

**Given** compatible type expressions
        **When** unification runs
        **Then** finds consistent substitution

        **Verification:** Unification works

**Given** expression
        **When** inference runs multiple times
        **Then** always produces same type

        **Lean Theorem:** infer_deterministic

        **Verification:** Determinism holds
