# Feature #40: Actors

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #40 |
| **Feature Name** | Actors |
| **Category** | Concurrency |
| **Difficulty** | 4 (Hard) |
| **Status** | Partial |
| **Implementation** | Rust |

## Description

Actor-based concurrency with spawn. Actors run in isolation with message passing. Default concurrency mode for Simple programs.

## Specification

[doc/spec/concurrency.md](../../spec/concurrency.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/runtime/src/value/actors.rs` | Actor runtime |
| `src/runtime/src/concurrency/mod.rs` | Concurrency scheduler |

## Syntax

```simple
# Define worker function
fn worker():
    return compute_something()

# Spawn actor
let handle = spawn worker()
```

## Actor Mode

Actor mode is the default concurrency mode:
- No `mut T` in function parameters
- Data is copied between actors
- Prevents data races by design

## Implementation Status

| Feature | Status |
|---------|--------|
| spawn | Complete |
| send/receive | Pending |
| actor state | Pending |
| supervision | Planned |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/concurrency/actors_spec.spl` | BDD spec (7 tests) |
| `src/driver/tests/runner_async_tests.rs` | Rust integration tests |

## Dependencies

- Depends on: #12
- Required by: None

## Notes

Actor mode is the default. Rejects mut T in parameters for data race safety. Send/receive pending implementation.
