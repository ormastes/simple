# Effect System Specification

**Evidence qualification (2026-10-21, SF6):** Reviewed against source commit `380200890ff030b34c68ff38f362b482e1276769`. Original dates and historical example/pass labels are retained as provenance, not a current execution result. This documentation correction ran no compiler, Lean, benchmark, or runtime tests; executable qualification is **UNRUN**.

Selected authority: `doc/02_requirements/language/mission_critical_profile.md`, REQ-MC-004 (lines 37–43), explicitly supersedes blanket “unsafe = all capabilities” for that profile: capability scope, reason, and reviewer manifest are required. This is a requirement with its stated phase, not evidence that every path enforces it.

Source anchors: `src/compiler/35.semantics/unsafe.spl` defines `UnsafeContext`, unsafe-operation classification, and context checks (lines 24–46, 82–117, 165–225); `src/compiler/00.common/assurance/unsafe_capabilities.spl` defines the scoped vocabulary (lines 30–51, 60–106). Their presence establishes source machinery, not complete enforcement in every compiler route. In particular `is_sffi_function` returns false for a bare `Var` (unsafe.spl:206–217); no blanket FFI-checker coverage is claimed. Effects and unsafe capabilities have distinct roles: the canonical vocabulary describes capabilities as permissions, not effects (`unsafe_capabilities.spl:30–35`). These historical effect examples do not prove that annotation alone validates operation preconditions. Legacy `expect true` examples are not current enforcement evidence.
*Source:* `test/03_system/feature/usage/effect_system_spec.spl`
**Feature IDs:** #EFFECT-SYS-001 to #EFFECT-SYS-040  |  **Category:** Type System | Effects  |  **Status:** Historical generated examples; current implementation qualification not established

## Overview



use std.text.{NL}

Tests the effect system including:
- @pure, @io, @net, @fs, @unsafe, @async effects
- Effect propagation and call restrictions
- Capability requirements and validation
- Stacked effects

## Effect Types

- `@pure` - No side effects, referentially transparent
- `@io` - Console/terminal I/O operations
- `@net` - Network operations
- `@fs` - File system operations
- `@unsafe` - Unsafe memory operations
- `@async` - Asynchronous operations

## Capabilities

- `requires [cap1, cap2]` - Module capability requirements
- Effect validation at compile time

## Syntax

```simple
requires [pure, io]

@pure
fn add(x: i64, y: i64) -> i64:
    x + y

@io @net
fn fetch_and_log(url: str) -> str:
    val data = http_get(url)
    print(data)
    data
```

## Feature: @pure Effect

## Pure Function Semantics

    Tests that @pure functions have no side effects.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | pure function can do computation | pass |
| 2 | pure function can call other pure functions | pass |
| 3 | pure function blocks print | pass |

**Example:** pure function can do computation
    Then  expect add(20, 22) == 42

**Example:** pure function can call other pure functions
    Then  expect quadruple(10) == 40

**Example:** pure function blocks print
    Then  expect true  # Compile-time check

## Feature: @io Effect

## I/O Function Semantics

    Tests that @io functions can perform I/O operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | io function can do computation | pass |

**Example:** io function can do computation
    Then  expect compute_and_return(21) == 42

## Feature: @async Effect

## Async Function Semantics

    Tests that @async decorator works like async fn.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | async decorator syntax works | pass |
| 2 | async allows non-blocking io | pass |

**Example:** async decorator syntax works
    Then  expect compute(21) == 42

**Example:** async allows non-blocking io
    Then  expect greet() == 42

## Feature: @fs Effect

## File System Function Semantics

    Tests that @fs functions can perform filesystem operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | fs function can do computation | pass |

**Example:** fs function can do computation
    Then  expect compute_fs(21) == 42

## Feature: @net Effect

## Network Function Semantics

    Tests that @net functions can perform network operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | net function can do computation | pass |

**Example:** net function can do computation
    Then  expect compute_net(21) == 42

## Feature: @unsafe Effect

## Unsafe Function Semantics

    Historical description superseded for the mission-critical profile by REQ-MC-004: `@unsafe` is not permission for arbitrary unchecked operations. The arithmetic example below demonstrates only its stated computation, not enforcement, FFI safety, or checker completeness.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | unsafe function can do computation | pass |

**Example:** unsafe function can do computation
    Then  expect compute_unsafe(21) == 42

## Feature: Stacked Effects

## Multiple Effect Decorators

    Tests that multiple effects can be stacked on one function.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | pure and async together | pass |
| 2 | io and net together | pass |
| 3 | all effects together | pass |
| 4 | all effects parsed | pass |

**Example:** pure and async together
    Then  expect fast_compute(21) == 42

**Example:** io and net together
    Then  expect network_logger(21) == 42

**Example:** all effects together
    Then  expect full_access(21) == 42

**Example:** all effects parsed
    Then  expect all_effects(42) == 42

## Feature: Effect with Attributes

## Effects and Attributes Together

    Tests effects with #[attribute] syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | effects with inline attribute | pass |

**Example:** effects with inline attribute
    Then  expect attributed_pure(21) == 42

## Feature: Unrestricted Functions

## Functions Without Effects

    Tests that functions without effects can do anything.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | unrestricted function works | pass |

**Example:** unrestricted function works
    Then  expect do_anything(21) == 42

## Feature: Effect Propagation

## Call Restrictions

    Tests that pure functions cannot call impure functions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | pure cannot call io | pass |
| 2 | pure cannot call net | pass |
| 3 | pure cannot call fs | pass |
| 4 | pure cannot call unsafe | pass |
| 5 | io can call pure | pass |
| 6 | io can call io | pass |
| 7 | unrestricted can call anything | pass |

**Example:** pure cannot call io
    Then  expect true  # Compile-time check

**Example:** pure cannot call net
    Then  expect true  # Compile-time check

**Example:** pure cannot call fs
    Then  expect true  # Compile-time check

**Example:** pure cannot call unsafe
    Then  expect true  # Compile-time check

**Example:** io can call pure
    Then  expect log_and_compute(20) == 50

**Example:** io can call io
    Then  expect caller(20) == 50

**Example:** unrestricted can call anything
    Then  expect unrestricted() == 65

## Feature: Capability Requirements

## requires Statement

    Tests the requires [cap] capability declaration.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | basic capability parsing | pass |
| 2 | multiple capabilities | pass |
| 3 | all capabilities | pass |
| 4 | trailing comma allowed | pass |
| 5 | empty requires list | pass |

**Example:** basic capability parsing
    Then  expect compute(21) == 42

**Example:** multiple capabilities
    Then  expect compute(21) == 42

**Example:** all capabilities
    Then  expect compute(21) == 42

**Example:** trailing comma allowed
    Then  expect compute(21) == 42

**Example:** empty requires list
    Then  expect compute(21) == 42

## Feature: Compile-Time Capability Validation

## Effect vs Capability Checking

    Tests that effects must match declared capabilities.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | effect matches capability | pass |
| 2 | io effect blocked by pure-only module | pass |
| 3 | async always allowed | pass |
| 4 | multiple effects with matching capabilities | pass |
| 5 | unrestricted module allows all | pass |

**Example:** effect matches capability
    Then  expect add(20, 22) == 42

**Example:** io effect blocked by pure-only module
    Then  expect true  # Compile-time check

**Example:** async always allowed
    Then  expect compute(21) == 42

**Example:** multiple effects with matching capabilities
    Then  expect process(21) == 42

**Example:** unrestricted module allows all
    Then  expect do_everything(21) == 42


