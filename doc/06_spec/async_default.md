# Async-Default Function Model

This document specifies Simple's async-default execution model where functions are async by default and sync is explicit.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #276-285 |
| Status | Draft |
| Source | `test/specs/async_default_spec.spl` |
| Updated | 2026-03-30 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 0 |
| Slow scenarios | 0 |
| Skipped scenarios | 16 |
| Pending scenarios | 0 |

**Keywords:** async, sync, effects, promises, futures
**Last Updated:** 2026-01-05
**Topics:** concurrency, syntax, effects
**Symbols:** Promise, Suspension, ExecutionMode, AsyncContext, Future
**Module:** simple_runtime::async
**Migrated From:** doc/06_spec/async_default.md

## Overview

This document specifies Simple's async-default execution model where functions are async by default and sync is explicit.

Functions without `sync` keyword return `Promise<T>` automatically. The suspension operator `~=` explicitly marks await points for readability and control.

## Design Principles

- **Async by default:** No `async` keyword required
- **Explicit suspension:** `~=` shows suspension points
- **Sync when needed:** `sync fn` for synchronous code
- **Type safety:** Promise types automatically inferred

## Related Specifications

- **Suspension Operator** - Explicit `~` suspension syntax
- **Concurrency** - Futures, actors, channels
- **Functions** - Function definitions
- **Type System** - Promise type inference

## Scenarios

- [skip] design_overview_3
- [skip] promise_type_6
- [skip] error_handling_36
- [skip] examples_32
- [skip] motivation
- [skip] syntax
- [skip] promise_type
- [skip] combinators
- [skip] sync_functions
- [skip] type_inference
- [skip] effect_inference
- [skip] interaction_with_suspension
- [skip] migration_strategy
- [skip] examples
- [skip] promise_type_details
- [skip] performance_considerations
