# Asynchronous Effects and Async/Await

> Asynchronous effects integrate Simple's effect system with async/await concurrency, allowing effectful computations to suspend and resume without blocking. This enables composable async pipelines where effects like logging, error handling, or I/O propagate through awaited call chains. This spec validates that async functions correctly carry and propagate effects across suspension points.

<details>
<summary>Full Scenario Manual</summary>

# Asynchronous Effects and Async/Await

Asynchronous effects integrate Simple's effect system with async/await concurrency, allowing effectful computations to suspend and resume without blocking. This enables composable async pipelines where effects like logging, error handling, or I/O propagate through awaited call chains. This spec validates that async functions correctly carry and propagate effects across suspension points.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RUNTIME-011 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/async_effects_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Asynchronous effects integrate Simple's effect system with async/await concurrency,
allowing effectful computations to suspend and resume without blocking. This enables
composable async pipelines where effects like logging, error handling, or I/O propagate
through awaited call chains. This spec validates that async functions correctly carry
and propagate effects across suspension points.

## Syntax

```simple
# Async effect propagation (planned)
async fn fetch_data(url: text) -> text with IO, Error:
use std.spec.step

val response = await http_get(url)
response.body

val result = await fetch_data("https://example.com")
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Async/Await | Syntax for non-blocking suspension and resumption of coroutines |
| Effect Propagation | Effects declared on async functions carry through await boundaries |
| Effect Handler | A construct that intercepts and processes effects from async computations |
| Suspension Point | A location where an async function yields control until a result is ready |

## Scenarios

### Async Effects


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `86d2b6097f7c3ef94058af22ce1be84735d1c8c24500421cb0f06daa1fddc89c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `86d2b6097f7c3ef94058af22ce1be84735d1c8c24500421cb0f06daa1fddc89c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `86d2b6097f7c3ef94058af22ce1be84735d1c8c24500421cb0f06daa1fddc89c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/feature/usage/async_effects_spec.spl
mirror: doc/06_spec/03_system/feature/usage/async_effects_spec.md (current)
findings: 4 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/03_system/feature/usage/async_effects_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/async_effects_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/async_effects_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/usage/async_effects_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
