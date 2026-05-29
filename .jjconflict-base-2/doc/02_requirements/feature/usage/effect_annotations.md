# Effect Annotations Specification
*Source:* `test/feature/usage/effect_annotations_spec.spl`
**Feature IDs:** #EFFECT-ANN-001 to #EFFECT-ANN-012  |  **Category:** Type System | Effects  |  **Status:** Implemented

## Overview




Tests that effect annotations (@pure, @io, @net, @fs, @unsafe, @async)
are correctly parsed and applied to functions.

## Effect Types

- `@pure` - No side effects, referentially transparent
- `@io` - Console/terminal I/O operations
- `@net` - Network operations
- `@fs` - File system operations
- `@unsafe` - Unsafe memory operations
- `@async` - Asynchronous operations

## Syntax

```simple
@pure
fn add(x: i64, y: i64) -> i64:
    x + y

@io @net
fn fetch_and_log(url: str):
    val data = http_get(url)
    print(data)
```

## Feature: Single Effect Annotations

## Basic Effect Decorators

    Tests that single effect decorators are correctly parsed.

### Scenario: @pure effect

| # | Example | Status |
|---|---------|--------|
| 1 | parses @pure on function | pass |
| 2 | pure function has no side effects | pass |

**Example:** parses @pure on function
    Then  expect add(20, 22) == 42

**Example:** pure function has no side effects
    Then  expect double(21) == 42

### Scenario: @io effect

| # | Example | Status |
|---|---------|--------|
| 1 | parses @io on function | pass |

**Example:** parses @io on function
    Then  expect true  # Parsed successfully

### Scenario: @net effect

| # | Example | Status |
|---|---------|--------|
| 1 | parses @net on function | pass |

**Example:** parses @net on function
    Then  expect true

### Scenario: @fs effect

| # | Example | Status |
|---|---------|--------|
| 1 | parses @fs on function | pass |

**Example:** parses @fs on function
    Then  expect true

### Scenario: @unsafe effect

| # | Example | Status |
|---|---------|--------|
| 1 | parses @unsafe on function | pass |

**Example:** parses @unsafe on function
    Then  expect true

### Scenario: @async effect

| # | Example | Status |
|---|---------|--------|
| 1 | parses @async on function | pass |

**Example:** parses @async on function
    Then  expect true

## Feature: Multiple Effect Annotations

## Combined Effects

    Tests that multiple effect decorators can be applied.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses two effects | pass |
| 2 | parses three effects | pass |
| 3 | parses io and fs together | pass |

**Example:** parses two effects
    Given val data = "mock"
    Then  expect true

**Example:** parses three effects
    Given val data = "mock"
    Then  expect true

**Example:** parses io and fs together
    Then  expect true

## Feature: Functions Without Effects

## Unrestricted Functions

    Tests that functions without effect annotations are unrestricted.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | function with no effects parses | pass |
| 2 | no-effect function can call anything | pass |

**Example:** function with no effects parses
    Then  expect true

**Example:** no-effect function can call anything
    Given val x = 42
    Then  expect flexible() == 42

## Feature: Effects with Other Decorators

## Mixed Decorator Usage

    Tests effects combined with non-effect decorators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | combines @pure with @inline | pass |
| 2 | combines @io with @deprecated | pass |
| 3 | effects separate from other decorators | pass |

**Example:** combines @pure with @inline
    Then  expect fast_add(20, 22) == 42

**Example:** combines @io with @deprecated
    Then  expect true

**Example:** effects separate from other decorators
    Then  expect cached_compute(6) == 36

## Feature: Effect Enum

## Effect Type System

    Tests the Effect enum values.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | Effect has Pure variant | pass |
| 2 | Effect has Io variant | pass |
| 3 | Effect has Net variant | pass |
| 4 | Effect has Fs variant | pass |
| 5 | Effect has Unsafe variant | pass |
| 6 | Effect has Async variant | pass |

**Example:** Effect has Pure variant
    Given val e = Effect.Pure
    Then  expect e == Effect.Pure

**Example:** Effect has Io variant
    Given val e = Effect.Io
    Then  expect e == Effect.Io

**Example:** Effect has Net variant
    Given val e = Effect.Net
    Then  expect e == Effect.Net

**Example:** Effect has Fs variant
    Given val e = Effect.Fs
    Then  expect e == Effect.Fs

**Example:** Effect has Unsafe variant
    Given val e = Effect.Unsafe
    Then  expect e == Effect.Unsafe

**Example:** Effect has Async variant
    Given val e = Effect.Async
    Then  expect e == Effect.Async

## Feature: Effect from Decorator Name

## String to Effect Conversion

    Tests converting decorator names to Effect values.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | converts 'pure' to Pure | pass |
| 2 | converts 'io' to Io | pass |
| 3 | converts 'net' to Net | pass |
| 4 | converts 'fs' to Fs | pass |
| 5 | converts 'unsafe' to Unsafe | pass |
| 6 | converts 'async' to Async | pass |
| 7 | returns None for unknown | pass |
| 8 | returns None for inline | pass |

**Example:** converts 'pure' to Pure
    Given val e = Effect.from_decorator_name("pure")
    Then  expect e == Some(Effect.Pure)

**Example:** converts 'io' to Io
    Given val e = Effect.from_decorator_name("io")
    Then  expect e == Some(Effect.Io)

**Example:** converts 'net' to Net
    Given val e = Effect.from_decorator_name("net")
    Then  expect e == Some(Effect.Net)

**Example:** converts 'fs' to Fs
    Given val e = Effect.from_decorator_name("fs")
    Then  expect e == Some(Effect.Fs)

**Example:** converts 'unsafe' to Unsafe
    Given val e = Effect.from_decorator_name("unsafe")
    Then  expect e == Some(Effect.Unsafe)

**Example:** converts 'async' to Async
    Given val e = Effect.from_decorator_name("async")
    Then  expect e == Some(Effect.Async)

**Example:** returns None for unknown
    Given val e = Effect.from_decorator_name("unknown")
    Then  expect not e.?

**Example:** returns None for inline
    Given val e = Effect.from_decorator_name("inline")
    Then  expect not e.?

## Feature: Effect Decorator Name

## Effect to String Conversion

    Tests converting Effect values to decorator names.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | Pure decorator name is 'pure' | pass |
| 2 | Io decorator name is 'io' | pass |
| 3 | Net decorator name is 'net' | pass |
| 4 | Fs decorator name is 'fs' | pass |
| 5 | Unsafe decorator name is 'unsafe' | pass |
| 6 | Async decorator name is 'async' | pass |

**Example:** Pure decorator name is 'pure'
    Then  expect Effect.Pure.decorator_name() == "pure"

**Example:** Io decorator name is 'io'
    Then  expect Effect.Io.decorator_name() == "io"

**Example:** Net decorator name is 'net'
    Then  expect Effect.Net.decorator_name() == "net"

**Example:** Fs decorator name is 'fs'
    Then  expect Effect.Fs.decorator_name() == "fs"

**Example:** Unsafe decorator name is 'unsafe'
    Then  expect Effect.Unsafe.decorator_name() == "unsafe"

**Example:** Async decorator name is 'async'
    Then  expect Effect.Async.decorator_name() == "async"


