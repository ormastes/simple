# Concurrency Features (#40-#43)

Async, parallel, and concurrent programming features.

## Features

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #40 | [Actors](0040_actors.md) | 4 | Partial | Rust |
| #41 | [Async/Await](0041_async_await.md) | 4 | Complete | Rust |
| #42 | [Generators](0042_generators.md) | 4 | Complete | Rust |
| #43 | [Futures](0043_futures.md) | 3 | Complete | Rust |

## Summary

**Status:** 3/4 Complete (75%)

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
