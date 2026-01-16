# HIR

*Source: `simple/std_lib/test/features/infrastructure/hir_spec.spl`*

---

# HIR

**Feature ID:** #4
**Category:** Infrastructure
**Difficulty:** 3/5
**Status:** Complete

## Overview

High-level IR for type checking and semantic analysis. Performs type inference, mutability checking, and capability verification after AST parsing.

## Syntax

HIR performs semantic analysis on:
- **Type Inference:** Determines types from usage context
- **Mutability Checking:** Verifies `val`/`var` semantics
- **Type Annotations:** Validates explicit type declarations
- **Type Narrowing:** Refines types in pattern matching branches
- **Method Resolution:** Resolves impl methods for structs

## Implementation

**Files:**
- `src/compiler/src/hir/mod.rs`
- `src/compiler/src/hir/types.rs`
- `src/compiler/src/hir/lower.rs`

**Test Files:**
- `src/driver/tests/runner_tests.rs`

**Dependencies:** #3 (AST)
**Required By:** #5 (MIR)

## Notes

HIR preserves source structure while adding type information. Validates semantic correctness before MIR lowering.
