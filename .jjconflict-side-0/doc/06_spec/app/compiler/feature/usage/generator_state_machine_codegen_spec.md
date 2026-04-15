# Generator State Machine Codegen Specification

Generator state machine codegen provides optimized code generation for generator functions that implement explicit state machines. This feature enables low-overhead coroutine semantics with fine-grained control over state transitions and stack frame management.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #800-805 |
| Category | Codegen |
| Difficulty | 4/5 |
| Status | In Progress |
| Source | `test/feature/usage/generator_state_machine_codegen_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Generator state machine codegen provides optimized code generation for generator functions
that implement explicit state machines. This feature enables low-overhead coroutine semantics
with fine-grained control over state transitions and stack frame management.

## Syntax

```simple
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
gen counter(max: Int) -> Int:
var i = 0
loop:
if i >= max:
break
yield i
i = i + 1
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/generator_state_machine_codegen/result.json` |

## Scenarios

- executes basic generator
- preserves local state across yields
- handles branched execution paths
- compiles loop-based generator
- allocates correct frame layout
- captures parameters in frame
- handles single-yield optimization
- compiles nested loop generator
