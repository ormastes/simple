# Pipeline Components Specification

**Feature ID:** #PIPELINE-COMP | **Category:** Infrastructure | **Status:** Implemented

_Source: `test/feature/usage/pipeline_components_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 17 |

## Test Structure

### Pipeline Creation and Composition

#### simple pipeline stages

- ✅ creates pipeline with single stage
- ✅ transforms data through pipeline
#### chaining stages

- ✅ chains multiple transformations
- ✅ chains filter then map then filter
### Pipeline Error Handling

#### error propagation

- ✅ propagates errors through stages
- ✅ stops processing on error
#### recovery from errors

- ✅ provides default on error
### Pipeline Buffering

#### buffer operations

- ✅ collects data in buffer
- ✅ respects buffer limits
#### draining buffers

- ✅ drains buffer completely
### Pipeline State

#### accumulating state

- ✅ maintains running total through stages
- ✅ accumulates with filter
#### state isolation

- ✅ keeps separate accumulators
### Pipeline Evaluation

#### eager evaluation

- ✅ evaluates immediately
- ✅ evaluates each transformation
#### terminal operations

- ✅ collects results from pipeline
- ✅ counts items in pipeline

