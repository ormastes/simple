# Pipeline Components Specification

Pipeline components provide a composable way to build data processing pipelines.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PIPELINE-COMP |
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/feature/usage/pipeline_components_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/pipeline_components/result.json` |

## Scenarios

- creates pipeline with single stage
- transforms data through pipeline
- chains multiple transformations
- chains filter then map then filter
- propagates errors through stages
- stops processing on error
- provides default on error
- collects data in buffer
- respects buffer limits
- drains buffer completely
- maintains running total through stages
- accumulates with filter
- keeps separate accumulators
- evaluates immediately
- evaluates each transformation
- collects results from pipeline
- counts items in pipeline
