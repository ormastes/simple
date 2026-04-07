# Aspect-Oriented Programming (AOP) Specification

Aspect-Oriented Programming (AOP) enables cross-cutting concern separation through

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AOP-001 to #AOP-020 |
| Category | Language |
| Status | In Progress |
| Source | `test/feature/usage/aop_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Tags:** aop

Aspect-Oriented Programming (AOP) enables cross-cutting concern separation through
compile-time weaving. AOP uses a unified predicate grammar with `pc{...}` pointcut
expressions that can match function executions, types, and attributes.

## Syntax

```simple
on pc{ execution(* target_func(..)) } use advice_func before priority 10

on pc{ execution(* target_func(..)) } use advice_func after_success priority 5

forbid pc{ import(test.internal.*) } "Production cannot import test internals"
allow pc{ depend(within(api.**), within(core.**)) } "API can depend on core"
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Advice | Code that executes at join points (before/after/around) |
| Pointcut | Expression defining where advice applies: `pc{...}` |
| Join point | Execution point where advice can be woven |
| Weaving | Process of inserting advice at join points |
| Priority | Integer controlling advice execution order |

## Behaviors

- Higher priority executes earlier for `before` advice
- Higher priority executes later for `after_*` advice
- `around` advice must call `proceed()` exactly once
- Zero overhead when AOP is not enabled
- Compile-time weaving for `before`/`after`, runtime for `around`

## Limitations (Current Implementation)

- Around advice is implemented through the runtime proceed contract and MIR weaving helpers
- Inline module definitions in test blocks not supported
- Runtime `init(...)` interception with `@inject` is covered in the Rust interpreter path; broader Simple-side DI/AOP authoring remains limited

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/aop/result.json` |

## Scenarios

- parses before advice with execution pointcut
- parses before advice with wildcard return type
- parses after_success advice
- parses after_error advice
- executes before advice before target
- executes after_success when target succeeds
- does not execute after_success when target returns Err
- executes after_error when target returns Err
- matches specific function name
- matches with wildcard in function name
- matches functions with specific attribute
- combines pointcuts with AND
- combines pointcuts with OR
- negates pointcuts with NOT
- declares forbidden import pattern
- declares forbidden dependency pattern
- declares allowed dependency pattern
- reports join points woven
- validates advice configuration
- function without advice has no weaving
- disabled weaving produces no diagnostics
