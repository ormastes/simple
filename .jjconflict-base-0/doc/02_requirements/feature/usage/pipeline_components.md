# Pipeline Components Specification
*Source:* `test/feature/usage/pipeline_components_spec.spl`
**Feature IDs:** #PIPELINE-COMP  |  **Category:** Infrastructure  |  **Status:** Implemented

## Overview



use std.text.{NL}

Pipeline components provide a composable way to build data processing pipelines.
They support chaining operations, handling errors, buffering data, and controlling
execution flow. Pipelines can be data-driven or event-driven and integrate with
the effects system for proper resource management.

## Syntax

```simple
val pipeline = source
    | filter(\x: x > 0)
    | map(\x: x * 2)
    | sink(print)
```

## Key Behaviors

- Pipeline stages compose with the pipe operator (|)
- Data flows through stages from left to right
- Error handling preserves error context through pipeline
- Backpressure controls data flow between stages
- Resources are managed through effect system
- Lazy evaluation defers computation until terminal operation

## Feature: Pipeline Creation and Composition

Verifies basic pipeline creation, stage composition, and data flow.
    Tests simple pipelines with single and multiple stages, and verifies
    that data passes through stages in correct order.

### Scenario: simple pipeline stages

| # | Example | Status |
|---|---------|--------|
| 1 | creates pipeline with single stage | pass |
| 2 | transforms data through pipeline | pass |

**Example:** creates pipeline with single stage
    Given val data = [1, 2, 3]
    Given val result = data
    Then  expect result.len() == 3

**Example:** transforms data through pipeline
    Given val data = [1, 2, 3]
    Given val result = data
    Then  expect result.len() == 3
    Then  expect result[0] == 2
    Then  expect result[1] == 4
    Then  expect result[2] == 6

### Scenario: chaining stages

| # | Example | Status |
|---|---------|--------|
| 1 | chains multiple transformations | pass |
| 2 | chains filter then map then filter | pass |

**Example:** chains multiple transformations
    Given val data = [1, 2, 3, 4, 5]
    Given val result = data
    Then  expect result.len() == 3
    Then  expect result[0] == 30
    Then  expect result[1] == 40
    Then  expect result[2] == 50

**Example:** chains filter then map then filter
    Given val data = [1, 2, 3, 4, 5, 6]
    Given val result = data
    Then  expect result.len() == 3

## Feature: Pipeline Error Handling

Verifies error handling and propagation through pipeline stages.
    Tests that errors are caught, propagated, and can be recovered from
    using error handlers and recovery strategies.

### Scenario: error propagation

| # | Example | Status |
|---|---------|--------|
| 1 | propagates errors through stages | pass |
| 2 | stops processing on error | pass |

**Example:** propagates errors through stages
    Given val result1 = safe_divide(2)
    Then  expect value == 50

**Example:** stops processing on error
    Given val data: List<i64> = [1, -2, 3]
    Given var results = []
    Then  expect results.len() == 2

### Scenario: recovery from errors

| # | Example | Status |
|---|---------|--------|
| 1 | provides default on error | pass |

**Example:** provides default on error
    Given val result1 = risky(5)
    Given val value1 = match result1:
    Then  expect value1 == 10
    Given val result2 = risky(0)
    Given val value2 = match result2:
    Then  expect value2 == -1

## Feature: Pipeline Buffering

Verifies buffering mechanisms that control data flow and backpressure
    between pipeline stages. Tests buffer capacity, overflow handling, and
    flushing strategies.

### Scenario: buffer operations

| # | Example | Status |
|---|---------|--------|
| 1 | collects data in buffer | pass |
| 2 | respects buffer limits | pass |

**Example:** collects data in buffer
    Given var buffer: List<i64> = []
    Given val data = [1, 2, 3]
    Then  expect buffer.len() == 3

**Example:** respects buffer limits
    Given val max_size = 5
    Given var buffer: List<i64> = []
    Given val data = [1, 2, 3, 4, 5, 6, 7]
    Then  expect buffer.len() == 5

### Scenario: draining buffers

| # | Example | Status |
|---|---------|--------|
| 1 | drains buffer completely | pass |

**Example:** drains buffer completely
    Given var buffer: List<i64> = [1, 2, 3]
    Given var drain_result = []
    Given val item = buffer[0]
    Then  expect drain_result.len() == 3

## Feature: Pipeline State

Verifies state management throughout pipeline execution. Tests
    accumulation of state across stages, state isolation between
    parallel executions, and state cleanup.

### Scenario: accumulating state

| # | Example | Status |
|---|---------|--------|
| 1 | maintains running total through stages | pass |
| 2 | accumulates with filter | pass |

**Example:** maintains running total through stages
    Given var total = 0
    Given val data = [1, 2, 3, 4, 5]
    Given val result = sum_values(data)
    Then  expect result == 15

**Example:** accumulates with filter
    Given var count = 0
    Given val data = [1, 2, 3, 4, 5]
    Then  expect count == 3

### Scenario: state isolation

| # | Example | Status |
|---|---------|--------|
| 1 | keeps separate accumulators | pass |

**Example:** keeps separate accumulators
    Given var result = 0
    Given val list1 = [1, 2, 3, 4, 5]
    Given val list2 = [10, 20, 30]
    Given val r1 = process_list(list1, 2)
    Given val r2 = process_list(list2, 15)
    Then  expect r1 == 12
    Then  expect r2 == 30

## Feature: Pipeline Evaluation

Verifies evaluation strategies for pipelines including lazy evaluation,
    eager evaluation, and terminal operations that trigger computation.

### Scenario: eager evaluation

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates immediately | pass |
| 2 | evaluates each transformation | pass |

**Example:** evaluates immediately
    Given val data = [1, 2, 3]
    Given val result = data
    Then  expect result[0] == 2
    Then  expect result[1] == 4

**Example:** evaluates each transformation
    Given var eval_count = 0
    Given val data = [1, 2, 3]
    Then  expect eval_count == 3

### Scenario: terminal operations

| # | Example | Status |
|---|---------|--------|
| 1 | collects results from pipeline | pass |
| 2 | counts items in pipeline | pass |

**Example:** collects results from pipeline
    Given val data = [1, 2, 3, 4, 5]
    Given val result = data
    Then  expect result.len() == 3

**Example:** counts items in pipeline
    Given val data = [1, 2, 3, 4, 5]
    Given val filtered = data
    Then  expect filtered.len() == 3


