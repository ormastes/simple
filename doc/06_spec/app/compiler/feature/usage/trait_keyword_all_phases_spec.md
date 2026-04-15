# Trait Keyword - All Phases

Comprehensive phase tests for the trait keyword feature covering all five phases: trait definition with method signatures (fn/me, parameters, return types), default method behavior, forwarding/delegation patterns, end-to-end workflows from trait definition through implementation to usage, and static dispatch via trait-bounded generics.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TRAIT-002 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/trait_keyword_all_phases_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Comprehensive phase tests for the trait keyword feature covering all
five phases: trait definition with method signatures (fn/me, parameters,
return types), default method behavior, forwarding/delegation patterns,
end-to-end workflows from trait definition through implementation to usage,
and static dispatch via trait-bounded generics.

## Syntax

```simple
trait Formatter:
    fn format(value: text) -> text
class TextFormatter:
    inner: BaseFormatter
```

Self-contained tests - no compiler-internal imports needed.
All types, traits, and functions are defined locally.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/trait_keyword_all_phases/result.json` |

## Scenarios

- trait declaration is recognized
- trait name is extracted correctly
- trait without methods acts as marker
- struct without trait impl has no trait methods
- finds two traits and implements both
- traits mixed with non-trait declarations work together
- correct trait impl is found for the right type
- type without matching trait impl uses own methods
- fn method is immutable and returns value
- fn method with return type works for multiple methods
- me method can mutate state
- mixed fn and me methods in same trait
- no-arg method works
- single-param method works
- multi-param method extracts all params correctly
- trait with only relevant methods works
- trait with associated type declaration works
- abstract method must be implemented
- default method is used when not overridden
- default method with inline body works
- overriding default method replaces it
- default method calls abstract method correctly
- all-abstract trait requires all methods implemented
- delegates immutable method to field
- delegates fn with args to field
- delegates mutable method to field
- forwards fn methods from trait to field
- forwards me methods from trait to field
- unknown trait generates no forwarding - wrapper has only own methods
- forwards all methods from field type
- define a trait, implement it, use methods
- complete define-implement-forward workflow
- multiple traits in source: each generates correct forwarding
- trait with default methods: only abstract methods need implementation
- trait scanner and forwarding agree on method count
- fn with trait-bounded param uses static dispatch
- multiple trait params dispatch correctly
- dyn Trait param uses dynamic dispatch
- interface-typed param dispatches at runtime
