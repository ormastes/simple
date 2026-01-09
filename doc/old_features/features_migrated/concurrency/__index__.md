# Concurrency Features (#40-#49)

Async, parallel, and concurrent programming features.

## Features

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #40 | [Actors](0040_actors.md) | 4 | Partial | Rust |
| #41 | [Async/Await](0041_async_await.md) | 4 | Complete | Rust |
| #42 | [Generators](0042_generators.md) | 4 | Complete | Rust |
| #43 | [Futures](0043_futures.md) | 3 | Complete | Rust |
| #44 | [Async Default](0044_async_default.md) | 3 | Planning | Rust |
| #45 | [Suspension Operator (~)](0045_suspension_operator.md) | 3 | Planning | Rust |
| #46 | [Effect Inference](0046_effect_inference.md) | 4 | Planning (Lean ✅) | Rust+Lean |
| #47 | [Promise Type](0047_promise_type.md) | 3 | Planning | Rust |

## Summary

**Status:** 3/8 Complete, 4/8 Planning with Lean verification (87.5% progress)

## Test Locations

- **Simple Tests:** `simple/std_lib/test/features/concurrency/`
- **Rust Tests:** `src/driver/tests/runner_async_tests.rs`

## Overview

The concurrency system provides multiple paradigms:
- **Actors**: Message-passing with spawn (default mode)
- **Async/Await**: Non-blocking I/O with async functions
- **Generators**: Lazy iteration with yield
- **Futures**: Promise-based async values

All modes respect the SC-DRF memory model guarantee.

## Async Default Implementation Plan

**Status:** Planning Phase (Lean verification complete)

A comprehensive 7-phase implementation plan is available in [async_default_implementation.md](../../plans/async_default_implementation.md).

**Lean Verification:**
- ✅ AsyncEffectInference.lean (265 lines, 10 theorems)
- ✅ Promise type system modeling
- ✅ Effect inference algorithm
- ✅ Type-driven await inference

**Next Steps:**
1. Phase 1: Parser support for `sync fn` keyword
2. Phase 2: Effect inference in type checker
3. Phase 3: Promise[T] standard library implementation
