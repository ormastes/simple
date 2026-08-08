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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Specification

## Scenarios

### ContextManager trait

#### keeps timer, lock, and transaction context managers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = context_manager_source()

expect(source).to_contain("class TimerContext:")
expect(source).to_contain("class Lock:")
expect(source).to_contain("enum TransactionState:")
expect(source).to_contain("class TransactionContext:")
```

</details>

#### keeps context enter and exit methods available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = context_manager_source()

expect(source).to_contain("me __enter__():")
expect(source).to_contain("me __exit__(exc_type, exc_value, traceback):")
expect(source).to_contain("fn is_running() -> bool")
expect(source).to_contain("fn is_completed() -> bool")
```

</details>

#### keeps wrapper and suppress helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = context_manager_source()

expect(source).to_contain("class ContextManagerWrapper:")
expect(source).to_contain("fn contextmanager(enter_fn, exit_fn) -> ContextManagerWrapper")
expect(source).to_contain("class SuppressContext:")
expect(source).to_contain("fn suppress(type1: text, type2: text) -> SuppressContext")
expect(source).to_contain("fn suppress_list(exception_types: [text]) -> SuppressContext")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ContextManager trait

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
