# Asynchronous Effects and Async/Await

> Asynchronous effects integrate Simple's effect system with async/await concurrency, allowing effectful computations to suspend and resume without blocking. This enables composable async pipelines where effects like logging, error handling, or I/O propagate through awaited call chains. This spec validates that async functions correctly carry and propagate effects across suspension points.

<!-- sdn-diagram:id=async_effects_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_effects_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_effects_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_effects_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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
