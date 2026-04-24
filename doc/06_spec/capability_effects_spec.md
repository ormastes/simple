# Capability-Based Effects Specification

This spec covers Simple's capability-based effect system, which statically tracks and enforces which effects (I/O, network, filesystem, pure computation) a function can perform. Capabilities are granted by callers and threaded through the call graph.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #140-165 |
| Status | Executable coverage |
| Source | `test/specs/capability_effects_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Keywords:** capabilities, effects, permissions, io, net, fs, pure
**Topics:** type-system, effects, security
**Symbols:** Capability, Effect, EffectSet, CapabilityGrant
**Module:** simple_compiler::effects

## Overview

This spec covers Simple's capability-based effect system, which statically
tracks and enforces which effects (I/O, network, filesystem, pure computation)
a function can perform. Capabilities are granted by callers and threaded
through the call graph.

Tests use local doubles to model capability grant/revoke, effect requirement
checking, propagation rules, and the distinction between pure and effectful
functions.

## Syntax

Declare effects a function requires:

    fn read_file(path: text) -> text requires fs:
        ...

    fn fetch_url(url: text) -> text requires net:
        ...

    fn add(a: i64, b: i64) -> i64:   # pure — no annotation needed
        a + b

Grant capabilities at a call site:

    with capabilities [io, net]:
        val page = fetch_url("http://example.com")

## Examples

    required_capability("io")   # => "io"
    required_capability("net")  # => "net"
    required_capability("fs")   # => "fs"
    required_capability("pure") # => ""  (pure needs no grant)

    val cap = Capability.new("io")
    cap.grant()
    cap.is_granted()  # => true
    cap.revoke()
    cap.is_granted()  # => false

    val effects = EffectSet.new()
    effects.add("io")
    effects.add("net")
    effects.requires("io")  # => true
    effects.is_pure()        # => false

## Key Concepts

**Capability** — an unforgeable token that grants permission to perform a
specific effect. Only code that holds the capability can invoke the effect.

**Effect** — a named category of side effect: `io`, `net`, `fs`, `alloc`,
`gpu`, or `pure`. Effect annotations appear in function signatures and are
checked at call sites.

**Propagation** — effects propagate transitively. If `f` calls `g` which
requires `net`, then `f` also requires `net` unless it holds or attenuates
the capability internally.

**Attenuation** — a holder can pass a restricted sub-capability to a callee
(e.g., read-only `fs` from a read-write `fs` capability).

**Pure functions** — functions with no effect annotations are pure; they
can be called anywhere including `const` contexts and spec evaluations.

**Effect polymorphism** — generic functions can quantify over effects:

    fn run<E>(action: fn() -> T requires E) -> T requires E:
        action()

This lets higher-order functions remain effect-transparent.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/capability_effects/summary.txt` |

## Scenarios

- features_1
- features_capability_inheritance
- features_effect_annotations
- features_effect_inference
- features_pure_by_default
- features_effect_propagation
- features_capability_requirements
- features_generic_effect_constraints
- features_error_messages
- features_effect_mismatch
- features_11
- features_stdlib_effects
- examples_pure_module
- examples_io_boundaries
