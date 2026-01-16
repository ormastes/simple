# Generator Codegen

*Source: `simple/std_lib/test/features/codegen/generator_codegen_spec.spl`*

---

# Generator Codegen

**Feature ID:** #96
**Category:** Codegen
**Difficulty:** Level 4/5
**Status:** Complete
**Implementation:** Rust

## Overview

Generator state machine code generation. Transforms generator functions with yield
statements into resumable state machines with dispatcher entry blocks.

## Syntax

```simple
val gen = generator(\: yield 42)
val value = next(gen)  # Returns 42

val multi = generator(\: [yield 1, yield 2, yield 3])
val collected = collect(multi)  # [1, 2, 3]
```

## Implementation

**Files:**
- src/compiler/src/mir/generator.rs - Generator state machine lowering
- src/compiler/src/mir/state_machine_utils.rs - State machine utilities
- src/compiler/src/codegen/instr_async.rs - Async instruction codegen

**Tests:**
- src/driver/tests/runner_async_tests.rs

**Dependencies:** Features #5, #42
**Required By:** None

## Notes

Generators are lowered to state machines with dispatcher + resume blocks. Liveness
analysis preserves values across suspension points.
