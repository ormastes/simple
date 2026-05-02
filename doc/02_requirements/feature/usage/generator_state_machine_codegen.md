# Generator State Machine Codegen Specification
*Source:* `test/feature/usage/generator_state_machine_codegen_spec.spl`
**Feature IDs:** #800-805  |  **Category:** Codegen  |  **Status:** In Progress

## Overview



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

## Feature: Generator State Machine - Basic

## Basic State Machine Compilation

    Tests basic generator state machine compilation and execution.

### Scenario: with simple sequential yields

### Scenario: Linear Generator Execution

        A generator with sequential yield points compiles to a linear state machine.

| # | Example | Status |
|---|---------|--------|
| 1 | executes basic generator | pass |

**Example:** executes basic generator
    Given val g = simple_gen()
    Then  expect(g()).to_equal(1)
    Then  expect(g()).to_equal(2)
    Then  expect(g()).to_equal(3)

### Scenario: with local variable preservation

### Scenario: State Frame Variables

        Local variables are preserved across yield points in the state frame.

| # | Example | Status |
|---|---------|--------|
| 1 | preserves local state across yields | pass |

**Example:** preserves local state across yields
    Given var i = 0
    Given val g = counter(3)
    Then  expect(g()).to_equal(0)
    Then  expect(g()).to_equal(1)
    Then  expect(g()).to_equal(2)

## Feature: Generator State Machine - Transitions

## State Transition Handling

    Tests proper handling of state transitions and branching.

### Scenario: with conditional branching

### Scenario: Branched State Paths

        Generators with conditional logic create branched state paths.

| # | Example | Status |
|---|---------|--------|
| 1 | handles branched execution paths | pass |

**Example:** handles branched execution paths
    Given val g1 = branched(true)
    Then  expect(g1.next()).to_equal(1)
    Then  expect(g1.next()).to_equal(2)
    Given val g2 = branched(false)
    Then  expect(g2.next()).to_equal(10)
    Then  expect(g2.next()).to_equal(20)

### Scenario: with loop state machines

### Scenario: Loop-Based Generators

        Loop constructs create loop-based state machines with state transitions.

| # | Example | Status |
|---|---------|--------|
| 1 | compiles loop-based generator | pass |

**Example:** compiles loop-based generator
    Given var i = 0
    Given val g = loop_gen(3)
    Then  expect(g.next()).to_equal(0)
    Then  expect(g.next()).to_equal(2)
    Then  expect(g.next()).to_equal(4)

## Feature: Generator State Machine - Stack Frames

## Stack Frame Layout and Management

    Tests stack frame allocation and variable preservation.

### Scenario: with multiple local variables

### Scenario: Complex State Frame

        Multiple local variables create complex state frame layouts.

| # | Example | Status |
|---|---------|--------|
| 1 | allocates correct frame layout | pass |

**Example:** allocates correct frame layout
    Given var a = 1
    Given var b = 2
    Given var c = 3
    Given val g = multi_var()
    Then  expect(g.next()).to_equal(3)  # 1 + 2
    Then  expect(g.next()).to_equal(5)  # 2 + 3
    Then  expect(g.next()).to_equal(4)  # 1 + 3

### Scenario: with captured parameters

### Scenario: Parameter Capture in Frame

        Function parameters are captured in the state frame.

| # | Example | Status |
|---|---------|--------|
| 1 | captures parameters in frame | pass |

**Example:** captures parameters in frame
    Given val g = param_gen(5, 3)
    Then  expect(g.next()).to_equal(5)
    Then  expect(g.next()).to_equal(3)
    Then  expect(g.next()).to_equal(8)

## Feature: Generator State Machine - Edge Cases

## Edge Case Handling

    Tests edge cases and special scenarios in state machine codegen.

### Scenario: with single yield

### Scenario: Trivial Generator

        Single-yield generators are optimized as special case.

| # | Example | Status |
|---|---------|--------|
| 1 | handles single-yield optimization | pass |

**Example:** handles single-yield optimization
    Given val g = single_yield()
    Then  expect(g.next()).to_equal(42)

### Scenario: with nested loops

### Scenario: Nested Loop State Machine

        Nested loops create multi-level state machines.

| # | Example | Status |
|---|---------|--------|
| 1 | compiles nested loop generator | pass |

**Example:** compiles nested loop generator
    Given var i = 0
    Given var j = 0
    Given val g = nested_loops(2)
    Then  expect(g.next()).to_equal(0)
    Then  expect(g.next()).to_equal(1)
    Then  expect(g.next()).to_equal(10)
    Then  expect(g.next()).to_equal(11)


