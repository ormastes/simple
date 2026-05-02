# Implementation Blocks Specification

Implementation blocks (`impl`) provide a flexible way to define methods for types outside of the type definition. This enables separation of concerns, method organization, and extension of types in different modules without modifying the original definition.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #830-835 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/impl_blocks_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Implementation blocks (`impl`) provide a flexible way to define methods for types outside
of the type definition. This enables separation of concerns, method organization, and
extension of types in different modules without modifying the original definition.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Impl Block | Collection of methods for a type |
| Instance Method | Methods that receive self as implicit parameter |
| Static Method | Methods that don't receive self |
| Method Organization | Grouping related behavior in impl blocks |

## Behavior

- Methods in impl blocks are part of the type's interface
- Impl blocks can be placed in any module or location
- Multiple impl blocks for the same type are merged
- Static methods are called with type name prefix
- Instance methods use dot notation on values

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/impl_blocks/result.json` |

## Scenarios

- defines methods in impl block
- defines multiple methods
- uses static factory method
- defines immutable methods
- defines mutable methods
- mixes static and instance methods
