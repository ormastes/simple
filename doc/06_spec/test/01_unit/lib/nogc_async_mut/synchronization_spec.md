# Synchronization Specification

> <details>

<!-- sdn-diagram:id=synchronization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=synchronization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

synchronization_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=synchronization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Synchronization Specification

## Scenarios

### Atomic-like operations

#### Basic load/store

#### creates value with initial state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atomic_val = 42
expect(atomic_val).to_equal(42)
```

</details>

#### stores and loads values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atomic_val = 10
atomic_val = 20
expect(atomic_val).to_equal(20)
```

</details>

#### swaps values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atomic_val = 30
val old_value = atomic_val
atomic_val = 40
expect(old_value).to_equal(30)
expect(atomic_val).to_equal(40)
```

</details>

#### Arithmetic operations

#### fetch_add pattern returns previous value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atomic_val = 100
val old_value = atomic_val
atomic_val = atomic_val + 5
expect(old_value).to_equal(100)
expect(atomic_val).to_equal(105)
```

</details>

#### fetch_sub pattern returns previous value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atomic_val = 100
val old_value = atomic_val
atomic_val = atomic_val - 10
expect(old_value).to_equal(100)
expect(atomic_val).to_equal(90)
```

</details>

#### increment and decrement

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = 0
counter = counter + 1
counter = counter + 1
counter = counter + 1
expect(counter).to_equal(3)
counter = counter - 1
expect(counter).to_equal(2)
```

</details>

### Mutex-like patterns

#### protects shared data

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shared_val = 0
# Simulate lock/modify/unlock
val locked = true
shared_val = shared_val + 1
val unlocked = true
expect(shared_val).to_equal(1)
```

</details>

#### sequential access maintains consistency

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var shared_val = 0
for _ in 0..10:
    shared_val = shared_val + 1
expect(shared_val).to_equal(10)
```

</details>

#### preserves data through multiple operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = {"value": 0}
data["value"] = 42
expect(data["value"]).to_equal(42)
data["value"] = data["value"] + 1
expect(data["value"]).to_equal(43)
```

</details>

### Counter patterns

#### counts up correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = 0
for i in 0..100:
    counter = counter + 1
expect(counter).to_equal(100)
```

</details>

#### counts with step

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = 0
for i in 0..50:
    counter = counter + 2
expect(counter).to_equal(100)
```

</details>

#### compare and swap pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var current = 10
val expected = 10
val desired = 20
if current == expected:
    current = desired
expect(current).to_equal(20)
```

</details>

#### compare and swap fails on mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var current = 15
val expected = 10
val desired = 20
if current == expected:
    current = desired
expect(current).to_equal(15)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/synchronization_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Atomic-like operations
- Mutex-like patterns
- Counter patterns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
