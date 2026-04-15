# Simple Language Type System - Test Specification

Executable tests for Simple's type system basics: primitives, mutability, generics, and type inference.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #20-29 |
| Status | Stable (Basic Features) |
| Source | `test/feature/usage/types_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Keywords:** types, mutability, type-inference
**Last Updated:** 2026-02-08
**Topics:** type-system
**Migrated From:** doc/06_spec/types.md

## Overview

Executable tests for Simple's type system basics: primitives, mutability, generics, and type inference.

Note: Advanced features (unit types, capability effects, suspension operators) are not yet implemented.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/types/result.json` |

## Scenarios

- basic type literals
- mutability rules - val and const
- mutable variables
- generic container - array
- option type basic usage
