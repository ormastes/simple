# With Statement Basic Specification

> 1. fn enter

<!-- sdn-diagram:id=with_statement_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=with_statement_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

with_statement_basic_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=with_statement_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# With Statement Basic Specification

## Scenarios

### with statement

#### calls enter and cleanup on simple context manager

1. fn enter
2. fn cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Define a simple context manager
class TestContext:
    entered: bool
    cleaned: bool

    fn enter() -> TestContext:
        self.entered = true
        self

    fn cleanup():
        self.cleaned = true

# Create context manager
val ctx = TestContext(entered: false, cleaned: false)

# Use with statement
with ctx as c:
    check c.entered

# Check cleanup was called
check ctx.cleaned
```

</details>

#### calls cleanup even when block completes normally

1. fn enter
2. fn cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cleanup_called = false

class TestContext:
    fn enter() -> TestContext:
        self

    fn cleanup():
        cleanup_called = true

val ctx = TestContext()

with ctx:
    val x = 42

check cleanup_called
```

</details>

#### supports variable binding with as clause

1. fn enter
2. fn cleanup
3.


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class ValueContext:
    value: text

    fn enter() -> text:
        self.value

    fn cleanup():
        ()

val ctx = ValueContext(value: "hello")

with ctx as val_:
    check val_ == "hello"
```

</details>

#### supports with statement without variable binding

1. fn enter
2. fn cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var enter_called = false
var cleanup_called = false

class NoBindContext:
    fn enter() -> NoBindContext:
        enter_called = true
        self

    fn cleanup():
        cleanup_called = true

val ctx = NoBindContext()

with ctx:
    check enter_called

check cleanup_called
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/with_statement_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- with statement

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
