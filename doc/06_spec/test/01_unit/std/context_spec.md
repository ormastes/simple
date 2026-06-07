# Context Specification

> <details>

<!-- sdn-diagram:id=context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Specification

## Scenarios

### ContextManager trait

#### keeps context-manager facade exports wired

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_context_source("src/lib/gc_async_mut/src/core/context_manager.spl")

expect(source).to_contain("TimerContext")
expect(source).to_contain("Timer")
expect(source).to_contain("Lock")
expect(source).to_contain("TransactionContext")
expect(source).to_contain("contextmanager")
expect(source).to_contain("suppress")
```

</details>

#### keeps compatibility facade wired to async context manager implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_context_source("src/lib/gc_sync_mut/src/core/context_manager.spl")

expect(source).to_contain("export use std.gc_async_mut.src.core.context_manager.*")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ContextManager trait

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
