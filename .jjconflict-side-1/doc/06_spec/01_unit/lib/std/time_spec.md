# time_spec

> Test suite for the std.time module, verifying time measurement and sleep functionality.

<!-- sdn-diagram:id=time_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=time_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

time_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=time_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# time_spec

Test suite for the std.time module, verifying time measurement and sleep functionality.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/time_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Test suite for the std.time module, verifying time measurement and sleep functionality.

## Scenarios

### Time Module

#### Time measurement

#### now_micros returns positive microseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = time_now_micros()
expect micros > 0
```

</details>

#### now_nanos returns positive nanoseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nanos = time_now_nanos()
expect nanos > 0
```

</details>

#### now_ms returns positive milliseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = time_now_ms()
expect ms > 0
```

</details>

#### now returns positive seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val secs = time_now()
expect secs > 0.0
```

</details>

#### nanos is approximately micros * 1000

1. expect diff abs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = time_now_micros()
val nanos = time_now_nanos()
# Should be within same millisecond (allowing for execution time)
val diff = (nanos / 1000) - micros
expect diff.abs() < 1000  # Within 1ms
```

</details>

#### ms is approximately micros / 1000

1. expect diff abs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = time_now_micros()
val ms = time_now_ms()
val diff = micros / 1000 - ms
expect diff.abs() < 2  # Within 2ms
```

</details>

#### elapsed time increases

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = time_now_micros()
# Busy wait a bit
var x = 0
for i in 0..1000:
    x = x + i
val end = time_now_micros()
expect end > start
```

</details>

#### elapsed time is measurable

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = time_now()
# Busy wait
var x = 0
for i in 0..10000:
    x = x + i
val elapsed = time_now() - start
expect elapsed > 0.0
```

</details>

#### Sleep functions

#### sleep pauses execution for specified duration

1. time sleep


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = time_now()
time_sleep(0.1)  # Sleep 100ms
val elapsed = time_now() - start
# Should be at least 100ms (0.1s)
# Allow up to 150ms due to OS scheduler
expect elapsed >= 0.09
expect elapsed <= 0.2
```

</details>

#### sleep_ms pauses for milliseconds

1. time sleep ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = time_now_ms()
time_sleep_ms(50)
val elapsed = time_now_ms() - start
expect elapsed >= 45  # At least 45ms
expect elapsed <= 100  # At most 100ms
```

</details>

#### sleep with zero duration does not crash

1. time sleep


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
time_sleep(0.0)
# Should complete without error
```

</details>

#### sleep_micros with small duration works

1. time sleep micros


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = time_now_micros()
time_sleep_micros(1000)  # 1ms
val elapsed = time_now_micros() - start
expect elapsed >= 500  # At least 0.5ms
expect elapsed <= 5000  # At most 5ms
```

</details>

#### Time conversions

#### microseconds to milliseconds conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros: i64 = 1000000  # 1 million microseconds
val ms = micros / 1000
expect ms == 1000  # 1000 milliseconds
```

</details>

#### milliseconds to seconds conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms: i64 = 5000
val secs = ms as f64 / 1000.0
expect secs == 5.0
```

</details>

#### nanoseconds to microseconds approximation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nanos: i64 = 1000000  # 1 million nanoseconds
val micros = nanos / 1000
expect micros == 1000
```

</details>

#### Edge cases

#### now functions work multiple times

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = time_now_micros()
val t2 = time_now_micros()
val t3 = time_now_micros()
expect t3 >= t2
expect t2 >= t1
```

</details>

#### time values are monotonic

1. var prev = time now micros


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var prev = time_now_micros()
for _ in 0..10:
    val curr = time_now_micros()
    expect curr >= prev
    prev = curr
```

</details>

#### very short sleep does not panic

1. time sleep
2. time sleep micros


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
time_sleep(0.001)  # 1ms
time_sleep_micros(100)  # 100 microseconds
# Should complete without error
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
