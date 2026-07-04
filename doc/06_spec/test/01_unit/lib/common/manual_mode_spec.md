# Manual Mode Specification

> <details>

<!-- sdn-diagram:id=manual_mode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=manual_mode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

manual_mode_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=manual_mode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Manual Mode Specification

## Scenarios

### Manual Mode Execution

#### is in manual mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = async_mode()
expect mode == "manual"
```

</details>

#### futures are pending until polled

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = future(42)
# In manual mode, future doesn't execute until polled
val completed = poll_future(f)
expect completed
expect await f == 42
```

</details>

#### polling multiple futures individually

- poll future
- poll future


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = future(10)
val f2 = future(20)
# Poll each future
poll_future(f1)
poll_future(f2)
expect await f1 == 10
expect await f2 == 20
```

</details>

#### await auto-polls in manual mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = future(100)
# await should auto-poll if needed
expect await f == 100
```

</details>

#### resolved futures work in manual mode

- expect is ready


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = resolved(42)
expect is_ready(f)
expect await f == 42
```

</details>

#### futures with captures in manual mode

- poll future


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 40
val f = future(base + 2)
poll_future(f)
expect await f == 42
```

</details>

#### computation in manual mode

- poll future


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = future(10 + 20 + 30)
poll_future(f)
expect await f == 60
```

</details>

#### multiple captures in manual mode

- poll future


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val c = 12
val f = future(a + b + c)
poll_future(f)
expect await f == 42
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/manual_mode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Manual Mode Execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
