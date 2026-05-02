# Type Inference Specification - Test Specification

Simple uses a Hindley-Milner-style type inference system that automatically deduces types for expressions, variables, and functions without requiring explicit type annotations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #13 |
| Status | Partial Implementation (Hindley-Milner scaffold working) |
| Type | Extracted Examples (Category B) |
| Reference | type_inference.md |
| Source | `test/specs/type_inference_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Last Updated:** 2026-02-08
**Migrated From:** doc/06_spec/type_inference.md

## Overview

Simple uses a Hindley-Milner-style type inference system that automatically deduces types
for expressions, variables, and functions without requiring explicit type annotations.

This test file covers basic type inference rules that work in the current runtime.

## Syntax

Type annotations are optional when the type can be inferred:

    val x = 42          # inferred: i64
    val y = 3.14        # inferred: f64
    val s = "hello"     # inferred: text
    val b = true        # inferred: bool

Function return types are inferred from the body:

    fn double(x: i64) -> _:   # _ = inferred i64
        x * 2

Generic instantiation inferred from arguments:

    fn identity<T>(x: T) -> T: x

    val a = identity(5)     # T inferred as i64
    val b = identity("hi")  # T inferred as text

Bidirectional inference from expected type:

    val nums: [i64] = [1, 2, 3]  # list element type inferred

## Examples

    val x = 42
    val y = x + 8    # => 50  (i64 propagated through arithmetic)

    val flag = x > 10    # => true  (bool from comparison)

    fn square(n: i64) -> i64: n * n
    square(7)   # => 49  (no annotation needed at call site)

    val words = ["a", "b", "c"]
    words.len()  # => 3  (list type inferred as [text])

## Key Concepts

**Hindley-Milner (HM)** — Simple's inference algorithm is based on HM with
extensions. Every expression has a principal type that is uniquely inferred
without programmer annotations (except at module boundaries for public APIs).

**Unification** — the inference engine collects equality constraints between
type variables and solves them. A conflict (e.g., using an `i64` where
`text` is expected) is caught at unification, not at run time.

**Generalization** — at let-bindings, free type variables are generalised
into universally quantified type schemes, enabling reuse with different
concrete types.

**Bidirectional inference** — expected types (from context) flow inward;
synthesised types (from expressions) flow outward. This reduces annotation
burden on lambda arguments and collection literals.

**Annotation escapes** — public API boundaries require explicit type
annotations so that library consumers get stable, documented types instead
of inferred internals that could change across versions.

**Rank-1 polymorphism** — Simple infers rank-1 (prenex) types by default.
Higher-rank types require explicit annotations and are rare in practice.

## Common Patterns

Let-bound generics (inferred at each use site):

    val id = |x| x         # type: <T> (T) -> T
    id(5)                   # => 5  (T = i64)
    id("hi")                # => "hi" (T = text)

Inference through `match`:

    val result = match flag:
        true  => 1
        false => 0

Collection literal with inferred element type:

    val nums = [1, 2, 3]    # [i64]
    val tags = ["a", "b"]   # [text]

Closure return type inferred from body:

    val square = |x: i64| x * x   # (i64) -> i64 — no annotation needed

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/type_inference/summary.txt` |

## Scenarios

- inference rules - literals
- inference rules - arithmetic
- inference rules - comparison
- inference rules - logical
- inference rules - bitwise
- inference rules - arrays
- inference rules - tuples
- inference rules - dictionaries
- inference rules - functions with explicit types
- inference rules - lambda types
- inference rules - higher-order functions
- inference rules - if expressions
- inference rules - loops
- examples - basic iteration
- examples - map function
- examples - option type with match
