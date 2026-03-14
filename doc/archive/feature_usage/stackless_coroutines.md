# Stackless Coroutines Specification
*Source:* `test/feature/usage/stackless_coroutines_spec.spl`
**Feature IDs:** #STACKLESS-CORO  |  **Category:** Runtime  |  **Status:** Implemented

## Overview



Stackless coroutines provide lightweight concurrency without allocating stack
space for each coroutine. They support async/await syntax, yield operations,
and generator functions.

## Feature: Generator Functions

Verifies generator function creation and iteration.

### Scenario: simple generators

| # | Example | Status |
|---|---------|--------|
| 1 | creates generator that yields values | pass |
| 2 | generator evaluates lazily | pass |

**Example:** creates generator that yields values
    Given var results = []

**Example:** generator evaluates lazily
    Given var count = 0
    Given var result = []
    Given val generated = counting_gen()

### Scenario: generator state

| # | Example | Status |
|---|---------|--------|
| 1 | preserves state across iterations | pass |
| 2 | generator with multiple yields | pass |

**Example:** preserves state across iterations
    Given var n = 0
    Given var result = []
    Given val values = stateful_gen()

**Example:** generator with multiple yields
    Given val results = multi_yield()

## Feature: Async/Await

Verifies async function creation and await semantics.
    Stubbed because async/await keywords are not supported by runtime parser.

### Scenario: basic async functions

| # | Example | Status |
|---|---------|--------|
| 1 | defines async function | pass |
| 2 | handles async computation | pass |

**Example:** defines async function
    Given val result = get_value()

**Example:** handles async computation
    Given val result = async_add(3, 4)

### Scenario: error handling in async

| # | Example | Status |
|---|---------|--------|
| 1 | chains async operations | pass |

**Example:** chains async operations
    Given val r1 = safe_divide(10, 2)

### Scenario: async resource management

## Feature: Yield Operations

Verifies yield semantics for generator functions.

### Scenario: basic yield

| # | Example | Status |
|---|---------|--------|
| 1 | yields single value | pass |
| 2 | yields multiple values | pass |

**Example:** yields single value
    Given val values = yield_one()

**Example:** yields multiple values
    Given val values = yield_range()

### Scenario: yield with computed values

| # | Example | Status |
|---|---------|--------|
| 1 | yields computed expressions | pass |
| 2 | yields based on conditions | pass |

**Example:** yields computed expressions
    Given var result = []
    Given val values = computed_yields()

**Example:** yields based on conditions
    Given var result = []
    Given val values = conditional_yields()

## Feature: Coroutine Scheduling

Verifies coroutine scheduling and context switching behavior.

### Scenario: multiple coroutines

| # | Example | Status |
|---|---------|--------|
| 1 | runs multiple generators | pass |

**Example:** runs multiple generators
    Given val g1 = gen1()
    Given val g2 = gen2()

### Scenario: efficient scheduling

| # | Example | Status |
|---|---------|--------|
| 1 | avoids stack allocation overhead | pass |
| 2 | handles many coroutines | pass |

**Example:** avoids stack allocation overhead
    Given var generators = []

**Example:** handles many coroutines
    Given var results = []

## Feature: Coroutine Lifecycle

Verifies the complete lifecycle of coroutines.

### Scenario: coroutine creation

| # | Example | Status |
|---|---------|--------|
| 1 | creates coroutine in initial state | pass |

**Example:** creates coroutine in initial state
    Given val coro = create_coro()

### Scenario: coroutine completion

| # | Example | Status |
|---|---------|--------|
| 1 | completes after yielding all values | pass |
| 2 | cleanup happens on completion | pass |

**Example:** completes after yielding all values
    Given val values = finite_gen()

**Example:** cleanup happens on completion
    Given var cleaned = false
    Given val _gen = cleanup_gen()

### Scenario: coroutine state transitions

| # | Example | Status |
|---|---------|--------|
| 1 | transitions from created to running | pass |
| 2 | transitions through suspend and resume | pass |
| 3 | transitions to completed | pass |

**Example:** transitions from created to running
    Given val coro = transitions()

**Example:** transitions through suspend and resume
    Given val values = suspend_resume()
    Given val first = values[0]

**Example:** transitions to completed
    Given val coro = completes()


