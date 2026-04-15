# Type Inference Specification - Test Specification

Simple uses a Hindley-Milner-style type inference system that automatically deduces types for expressions, variables, and functions without requiring explicit type annotations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #13 |
| Status | Partial Implementation (Hindley-Milner scaffold working) |
| Source | `test/specs/type_inference_spec.spl` |
| Updated | 2026-03-30 |
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
