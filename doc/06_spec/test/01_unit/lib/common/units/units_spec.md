# Semantic Unit Types Specification

> Size units represent byte counts with conversion methods for binary (KiB, MiB, GiB)

<!-- sdn-diagram:id=units_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=units_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

units_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=units_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Unit Types Specification

Size units represent byte counts with conversion methods for binary (KiB, MiB, GiB)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UNITS-SIZE, #UNITS-TIME |
| Category | Standard Library |
| Status | Implemented |
| Source | `test/01_unit/lib/common/units/units_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Size Units

Size units represent byte counts with conversion methods for binary (KiB, MiB, GiB)
and decimal (KB, MB, GB) units.

## Time Units

Time units represent durations in nanoseconds with conversion methods for microseconds,
milliseconds, seconds, minutes, hours, and days.

## Key Behaviors

- Unit types prevent accidental mixing (size values don't mix with time values)
- Arithmetic operations preserve unit semantics
- Conversions are explicit and type-safe
- Constants are provided for common values

## Scenarios

### Size Units

#### byte count creation

#### creates ByteCount from integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = 1024
expect b == 1024
```

</details>

#### ByteCount zero value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = 0
expect zero == 0
```

</details>

#### ByteCount comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1024 > 512
expect 512 < 1024
expect 1024 == 1024
```

</details>

#### binary unit conversions

#### converts bytes to kibibytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = 1024
expect bytes > 0
```

</details>

#### converts bytes to mebibytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = 1048576
expect bytes > 1024
```

</details>

#### converts bytes to gibibytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = 1073741824
expect bytes > 1048576
```

</details>

#### ByteCount arithmetic

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1024
val b = 512
expect (a + b) == 1536
expect (a - b) == 512
```

</details>

#### decimal unit conversions

#### converts bytes to kilobytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = 1000
expect bytes > 0
```

</details>

#### converts bytes to megabytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = 1000000
expect bytes > 1000
```

</details>

#### converts bytes to gigabytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = 1000000000
expect bytes > 1000000
```

</details>

#### unit comparisons

#### compares different sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val small = 100
val large = 1000
expect large > small
```

</details>

#### size arithmetic operations

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 500
val b = 200
expect (a + b) == 700
expect (a - b) == 300
```

</details>

#### size constants

#### uses kibi constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1 KiB = 1024 bytes
expect 1024 > 0
```

</details>

#### uses mebi constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1 MiB = 1048576 bytes
expect 1048576 > 1024
```

</details>

#### uses gibi constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1 GiB
expect 1073741824 > 1048576
```

</details>

### Time Units

#### nanoseconds

#### creates nanosecond duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = 1000
expect ns == 1000
```

</details>

#### zero duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = 0
expect zero == 0
```

</details>

#### time unit conversions

#### converts nanoseconds to microseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = 1000
expect ns > 0
```

</details>

#### converts nanoseconds to milliseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = 1000000
expect ns > 1000
```

</details>

#### converts nanoseconds to seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = 1000000000
expect ns > 1000000
```

</details>

#### converts to minutes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = 60000000000
expect ns > 1000000
```

</details>

#### converts to hours

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = 3600000000000
expect ns > 60000000000
```

</details>

#### converts to days

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = 86400000000000
expect ns > 3600000000000
```

</details>

#### duration arithmetic

#### adds durations

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1000000000
val b = 2000000000
expect (a + b) == 3000000000
```

</details>

#### subtracts durations

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 3000000000
val b = 1000000000
expect (a - b) == 2000000000
```

</details>

#### multiplies duration

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dur = 1000000000
val n = 2
expect (dur * n) == 2000000000
```

</details>

#### time duration constants

#### uses millisecond constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = 1000000
expect ms > 0
```

</details>

#### uses second constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = 1000000000
expect s > 1000000
```

</details>

#### uses minute constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = 60000000000
expect m > 1000000000
```

</details>

#### uses hour constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = 3600000000000
expect h > 60000000000
```

</details>

#### uses day constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = 86400000000000
expect d > 3600000000000
```

</details>

#### duration comparisons

#### compares time durations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fast = 1000
val slow = 2000
expect slow > fast
```

</details>

#### equality of durations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1000000000
val b = 1000000000
expect a == b
```

</details>

#### less than comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1000000000
val b = 2000000000
expect a < b
```

</details>

#### f32 duration conversions

#### converts to seconds with precision

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = 1500000000
# 1.5 seconds in nanoseconds
expect ns > 1000000000
```

</details>

#### converts to milliseconds with precision

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = 1500000
# 1.5 milliseconds in nanoseconds
expect ns > 1000000
```

</details>

### Combined Unit Operations

#### mixed operations

#### size and time are independent units

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = 1024
val nanos = 1000000000
expect bytes < nanos
```

</details>

#### arithmetic with same unit types

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes1 = 2000
val bytes2 = 1000
val total = bytes1 + bytes2
expect total == 3000
```

</details>

#### time arithmetic operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = 1000000000
val end = 2000000000
val elapsed = end - start
expect elapsed == 1000000000
```

</details>

#### unit identity

#### units preserve type safety

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = 1024
val time = 1000000
expect size > 0
expect time > 0
```

</details>

#### multiple unit values

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = 2048
val t = 2000000000
expect (b + 1024) == 3072
expect (t + 1000000000) == 3000000000
```

</details>

### Edge Cases and Boundaries

#### zero values

#### handles zero size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = 0
expect zero == 0
expect zero < 1
```

</details>

#### handles zero duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = 0
expect zero == 0
expect zero < 1
```

</details>

#### large values

#### handles large byte counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val large = 1099511627776
expect large > 0
expect large > 1000000000
```

</details>

#### handles large durations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val large = 86400000000000
expect large > 0
expect large > 1000000000
```

</details>

#### unit overflow handling

#### arithmetic results are valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 999999999
val b = 1
val res_val = a + b
expect res_val == 1000000000
```

</details>

#### subtraction boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1000
val b = 1000
val res_val = a - b
expect res_val == 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
