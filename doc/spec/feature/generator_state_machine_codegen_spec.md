# Generator State Machine Codegen Specification

**Feature ID:** #800-805 | **Category:** Codegen | **Difficulty:** 4/5 | **Status:** In Progress

_Source: `test/feature/usage/generator_state_machine_codegen_spec.spl`_

---

## Overview

Generator state machine codegen provides optimized code generation for generator functions
that implement explicit state machines. This feature enables low-overhead coroutine semantics
with fine-grained control over state transitions and stack frame management.

## Syntax

```simple
# Generator with explicit state machine
gen fibonacci() -> Int:
    var a = 0
    var b = 1

    loop:
        yield a
        val temp = a + b
        a = b
        b = temp
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| State Machine | Explicit representation of generator execution state |
| Yield Point | Location where generator suspends and resumes |
| Stack Frame | Preserved local state between yield points |
| Codegen Optimization | Direct state machine compilation without trampolining |

## Behavior

- Generator functions compile to explicit state machine data structures
- Each yield point corresponds to a state transition
- Local variables preserved across yield points in the state frame
- Type-safe state representation with discriminant unions
- Zero-copy variable capture where possible

## Related Specifications

- [Generators](../generators/generators_spec.spl) - Generator syntax and semantics
- [Coroutines](../coroutines/coroutines_spec.spl) - Coroutine implementation
- [Memory Management](../memory_management/memory_management_spec.spl) - Stack frame management

## Implementation Notes

State machine codegen targets:
- Direct MIR emission for state transitions
- Optimized codegen for single-yield common case
- Frame layout analyzed for memory efficiency
- Stack allocation preferred over heap when possible

## Examples

```simple
# Simple state machine generator
gen counter(max: Int) -> Int:
    var i = 0
    loop:
        if i >= max:
            break
        yield i
        i = i + 1
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 8 |

## Test Structure

### Generator State Machine - Basic

#### with simple sequential yields

- ✅ executes basic generator
#### with local variable preservation

- ✅ preserves local state across yields
### Generator State Machine - Transitions

#### with conditional branching

- ✅ handles branched execution paths
#### with loop state machines

- ✅ compiles loop-based generator
### Generator State Machine - Stack Frames

#### with multiple local variables

- ✅ allocates correct frame layout
#### with captured parameters

- ✅ captures parameters in frame
### Generator State Machine - Edge Cases

#### with single yield

- ✅ handles single-yield optimization
#### with nested loops

- ✅ compiles nested loop generator

