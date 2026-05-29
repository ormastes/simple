# Capture Buffer and Virtual Register Remapping Specification
*Source:* `test/feature/usage/capture_buffer_vreg_remapping_spec.spl`
**Feature IDs:** #VREGMAP-001 to #VREGMAP-020  |  **Category:** Runtime | Memory Management  |  **Status:** Planned

## Overview


use std.text.{NL}

## Overview

This specification covers advanced virtual register (vreg) remapping and capture
buffer management at the runtime level. These are internal optimization features
that affect how the interpreter manages memory and registers during function
execution.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Virtual Register (vreg) | Compiler-internal register representing values during execution |
| Capture Buffer | Runtime buffer capturing values into closure/lambda scopes |
| Remapping | Optimization to reuse vregs across code regions |
| Live Range | Set of instructions where a vreg is actively used |
| Interference | Two vregs conflict if their live ranges overlap |

## Behavior

- Virtual registers are allocated for each value in the program
- Capture buffers copy values from outer scope into closure scope
- Remapping allows vregs to be reused when live ranges don't overlap
- Optimization reduces memory pressure and improves cache locality
- All changes are transparent to the user - language behavior unchanged

## Related Specifications

- [Closures and Lambdas](closures_spec.spl) - Capture semantics
- [Memory Management](memory_management_spec.spl) - GC and allocation
- [Function Calls](function_calls_spec.spl) - Call conventions

## Feature: Capture Buffer Creation

## Basic Capture Buffer Creation

    Tests that capture buffers are created correctly when closures capture
    variables from outer scope.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates capture buffer for single captured variable | pass |
| 2 | creates capture buffer for multiple variables | pass |
| 3 | captures variable in nested closure | pass |
| 4 | captures in lambda with parameters | pass |

**Example:** creates capture buffer for single captured variable
    Given val x = 10
    Given val closure = \: x
    Then  expect closure() == 10

**Example:** creates capture buffer for multiple variables
    Given val a = 5
    Given val b = 15
    Given val closure = \: a + b
    Then  expect closure() == 20

**Example:** captures variable in nested closure
    Given val outer = 100
    Given val f = \: \: outer
    Given val inner = f()
    Then  expect inner() == 100

**Example:** captures in lambda with parameters
    Given val factor = 2
    Given val double = \x: x * factor
    Then  expect double(5) == 10

## Feature: Capture Buffer Scope Isolation

## Capture Buffer Scope Isolation

    Tests that captured buffers correctly isolate values from different scopes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | captures value at definition time | pass |
| 2 | captures in loop iteration | pass |
| 3 | captures different scopes separately | pass |

**Example:** captures value at definition time
    Given val x = 10
    Given val closure = \: x
    Then  expect closure() == 10

**Example:** captures in loop iteration
    Given var closures = []
    Then  expect closures.len() == 3

**Example:** captures different scopes separately
    Given val x = 1
    Given val f = \: x
    Given val y = 2
    Given val g = \: y
    Then  expect f() == 1
    Then  expect g() == 2

## Feature: Virtual Register Allocation

## Virtual Register Allocation

    Tests basic virtual register allocation for values.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allocates vreg for simple variable | pass |
| 2 | allocates vreg for expression result | pass |
| 3 | allocates vregs for multiple values | pass |
| 4 | allocates vreg for array element | pass |

**Example:** allocates vreg for simple variable
    Given val x = 42
    Then  expect x == 42

**Example:** allocates vreg for expression result
    Given val result = 10 + 20
    Then  expect result == 30

**Example:** allocates vregs for multiple values
    Given val a = 1
    Given val b = 2
    Given val c = 3
    Then  expect a + b + c == 6

**Example:** allocates vreg for array element
    Given val arr = [10, 20, 30]
    Given val first = arr[0]
    Then  expect first == 10

## Feature: Virtual Register Reuse

## Virtual Register Reuse

    Tests that virtual registers are reused when values don't interfere.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | reuses vreg in sequential statements | pass |
| 2 | reuses vreg after value is no longer needed | pass |
| 3 | does not reuse interfering vregs | pass |
| 4 | reuses vregs in branches | pass |

**Example:** reuses vreg in sequential statements
    Given val a = 10
    Given val b = 20          # a is dead, can reuse its vreg
    Then  expect b == 20

**Example:** reuses vreg after value is no longer needed
    Given var x = 5
    Then  expect x == 15

**Example:** does not reuse interfering vregs
    Given val a = 10
    Given val b = a + 20      # a is still live, must use different vreg
    Then  expect b == 30

**Example:** reuses vregs in branches
    Given val cond = true
    Given val x = if cond: 10 else: 20
    Then  expect x == 10

## Feature: Live Range Analysis

## Live Range Analysis

    Tests correct identification of variable live ranges.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | detects live range of simple variable | pass |
| 2 | detects live range extends to final use | pass |
| 3 | detects live range ends after last use | pass |
| 4 | handles nested live ranges | pass |

**Example:** detects live range of simple variable
    Given val x = 5
    Given val y = x + 1       # x is live here
    Then  expect y == 6

**Example:** detects live range extends to final use
    Given val a = 10
    Given val b = 20
    Given val c = a + b       # Both a and b are live
    Then  expect c == 30

**Example:** detects live range ends after last use
    Given val temp = 100
    Given val result = temp * 2  # temp is dead after this
    Then  expect result == 200

**Example:** handles nested live ranges
    Given val outer = 5
    Given val inner = outer + 10
    Given val combined = outer + inner
    Then  expect combined == 20

## Feature: Register Remapping in Loops

## Register Remapping in Loops

    Tests virtual register remapping optimization in loop contexts.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | remaps vregs in loop iterations | pass |
| 2 | handles nested loops with remapping | pass |
| 3 | preserves values across loop iterations | pass |

**Example:** remaps vregs in loop iterations
    Given var sum = 0
    Given val local = i * 2    # Can reuse vreg each iteration
    Then  expect sum == 12

**Example:** handles nested loops with remapping
    Given var count = 0
    Then  expect count == 4

**Example:** preserves values across loop iterations
    Given var accumulated = []
    Then  expect accumulated.len() == 3

## Feature: Capture Buffer with Remapped Registers

## Capture Buffer with Remapped Registers

    Tests interaction between capture buffers and vreg remapping.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | captures value despite vreg reuse | pass |
| 2 | captures multiple values with remapping | pass |
| 3 | captures in loop with vreg remapping | pass |

**Example:** captures value despite vreg reuse
    Given val captured = 42
    Given val closure = \: captured
    Then  expect closure() == 42

**Example:** captures multiple values with remapping
    Given val a = 10
    Given val b = 20
    Given val f = \: a + b
    Then  expect f() == 30

**Example:** captures in loop with vreg remapping
    Given var closures = []
    Given val current = i
    Then  expect closures.len() == 3

## Feature: Register Interference Detection

## Register Interference Detection

    Tests that interference between vregs is correctly identified.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | detects interference between live ranges | pass |
| 2 | detects no interference for sequential values | pass |
| 3 | handles complex interference patterns | pass |

**Example:** detects interference between live ranges
    Given val a = 10
    Given val b = a + 5       # a interferes with b
    Given val c = a + b       # All three interfere
    Then  expect c == 25

**Example:** detects no interference for sequential values
    Given val a = 10
    Given val _ = a
    Given val b = 20          # No interference - a is dead
    Then  expect b == 20

**Example:** handles complex interference patterns
    Given val a = 1
    Given val b = a + 1
    Given val c = a + b
    Given val d = b + c
    Then  expect d == 5

## Feature: Capture Buffer Cleanup

## Capture Buffer Cleanup

    Tests that capture buffers are properly managed during execution.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | maintains captured values across calls | pass |
| 2 | isolates different capture buffers | pass |
| 3 | handles closure returning closure | pass |

**Example:** maintains captured values across calls
    Given val base = 100
    Given val add = \x: base + x
    Then  expect add(5) == 105
    Then  expect add(10) == 110
    Then  expect add(5) == 105

**Example:** isolates different capture buffers
    Given val f1 = make_closure(1)
    Given val f2 = make_closure(2)
    Then  expect f1() == 1
    Then  expect f2() == 2

**Example:** handles closure returning closure
    Given val make_adder = {NL}: \x: n + x
    Given val add5 = make_adder(5)
    Then  expect add5(3) == 8

## Feature: Register Spillage

## Register Spillage

    Tests behavior when too many values are live (spillage to stack/memory).

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles many live values | pass |
| 2 | handles complex expressions with many values | pass |

**Example:** handles many live values
    Given val a = 1
    Given val b = 2
    Given val c = 3
    Given val d = 4
    Given val e = 5
    Given val result = a + b + c + d + e
    Then  expect result == 15

**Example:** handles complex expressions with many values
    Given val result = ((1 + 2) * (3 + 4)) + ((5 + 6) * (7 + 8))
    Then  expect result == 186

## Feature: Register Preservation Across Calls

## Register Preservation Across Calls

    Tests that values are preserved across function calls.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | preserves local values across function call | pass |
| 2 | preserves values in nested calls | pass |

**Example:** preserves local values across function call
    Given val a = 10
    Given val b = double(5)
    Given val c = a + b
    Then  expect c == 20

**Example:** preserves values in nested calls
    Given val base = 5
    Given val result = g(base)
    Then  expect result == 12

## Feature: Optimization Observable Effects

## Optimization Observable Effects

    Tests that optimization doesn't change observable behavior.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | produces correct result after vreg reuse | pass |
| 2 | preserves value semantics | pass |
| 3 | maintains mutation semantics | pass |

**Example:** produces correct result after vreg reuse
    Given val arr = [1, 2, 3, 4, 5]
    Given var sum = 0
    Then  expect sum == 15

**Example:** preserves value semantics
    Given val x = 42
    Given val y = x
    Then  expect y == 42

**Example:** maintains mutation semantics
    Given var count = 0
    Then  expect count == 2

## Feature: Closure Capture Edge Cases

## Closure Capture Edge Cases

    Tests edge cases in capture buffer handling.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | captures in deeply nested closures | pass |
| 2 | captures the same variable multiple times | pass |
| 3 | captures from multiple scopes via lambda | pass |

**Example:** captures in deeply nested closures
    Given val deep_val = 1
    Given val deep_fn1 = \: deep_val
    Given val deep_fn2 = \: deep_fn1()
    Given val deep_fn3 = \: deep_fn2()
    Then  expect deep_fn3() == 1

**Example:** captures the same variable multiple times
    Given val triple_val = 10
    Given val triple_fn = \: triple_val + triple_val + triple_val
    Then  expect triple_fn() == 30

**Example:** captures from multiple scopes via lambda
    Given val outer = 100
    Given val make_inner = \:
    Given val inner = outer + 1
    Given val inner_f = make_inner()
    Then  expect inner_f() == 101

## Feature: Capture Buffer Memory Layout

## Capture Buffer Memory Layout

    Tests that capture buffers maintain correct memory alignment.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | stores mixed-type captures | pass |
| 2 | captures different sized values | pass |

**Example:** stores mixed-type captures
    Given val i = 10
    Given val f = 3.14
    Given val s = "text"
    Given val closure = \: "{i}, {f}, {s}"
    Given val result = closure()
    Then  expect result == "10, 3.14, text"

**Example:** captures different sized values
    Given val a: i32 = 1
    Given val b: i64 = 2
    Given val closure = \: a + b
    Then  expect closure() == 3

## Feature: Performance Characteristics

## Performance Characteristics

    Tests performance-related behavior (correctness, not timing).

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | processes many captures efficiently | pass |
| 2 | handles array of closures | pass |
| 3 | processes filtered captures | pass |

**Example:** processes many captures efficiently
    Given val values = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    Given var sum = 0
    Then  expect sum == 55

**Example:** handles array of closures
    Given var closures = []
    Given val current = i
    Then  expect closures.len() == 5

**Example:** processes filtered captures
    Given val values = [1, 2, 3, 4, 5]
    Given val evens = values.filter(\x: x % 2 == 0)
    Then  expect evens.len() == 2


