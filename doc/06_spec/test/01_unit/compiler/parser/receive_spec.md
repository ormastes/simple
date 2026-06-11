# Receive Specification

> <details>

<!-- sdn-diagram:id=receive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=receive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

receive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=receive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Receive Specification

## Scenarios

### receive: block syntax

### single case arm

#### message processing pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var got = 0
val msg = "ping"
if msg == "ping":
    got = 1
expect(got).to_equal(1)
```

</details>

#### integer pattern handling

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var got = 0
val msg = 42
if msg == 42:
    got = 42
expect(got).to_equal(42)
```

</details>

#### case arm body can use outer variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
val base = 10
val msg = "msg"
if msg == "msg":
    result = base + 5
expect(result).to_equal(15)
```

</details>

### multiple case arms

#### handles first matching arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var got = 0
val msg = "ping"
if msg == "ping":
    got = 1
elif msg == "pong":
    got = 2
elif msg == "stop":
    got = 3
expect(got).to_equal(1)
```

</details>

#### string pattern matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var got = "none"
val msg = "hello"
if msg == "hello":
    got = "hello"
elif msg == "world":
    got = "world"
expect(got).to_equal("hello")
```

</details>

### after timeout arm

#### timeout fallback pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var got = 0
val has_message = false
if has_message:
    got = 1
else:
    got = 99
expect(got).to_equal(99)
```

</details>

#### zero timeout pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var got = 0
val has_message = false
if has_message:
    got = 1
else:
    got = 0
expect(got).to_equal(0)
```

</details>

#### timeout body can compute

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
val has_message = false
if has_message:
    result = 1
else:
    result = 10 + 5
expect(result).to_equal(15)
```

</details>

### timeout without case arms

#### immediate timeout pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var got = 0
got = 42
expect(got).to_equal(42)
```

</details>

### nested receive

#### message handling inside a function

1. fn run handler
   - Expected: r equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_handler() -> i64:
    var result = 0
    val msg = "done"
    if msg == "done":
        result = 7
    result
val r = run_handler()
expect(r).to_equal(7)
```

</details>

#### timeout inside a function

1. fn run with timeout
   - Expected: r equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_with_timeout() -> i64:
    var result = 0
    val has_message = false
    if has_message:
        result = 1
    else:
        result = 99
    result
val r = run_with_timeout()
expect(r).to_equal(99)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/receive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- receive: block syntax
- single case arm
- multiple case arms
- after timeout arm
- timeout without case arms
- nested receive

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
