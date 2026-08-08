# Time Utilities Specification

> This specification covers comprehensive time and duration utility functions: 1. Duration creation and manipulation (millis, seconds, minutes, hours, days) 2. Duration arithmetic (add, subtract, multiply, divide) 3. Duration parsing from strings (e.g., "1h30m45s") 4. Duration formatting and display 5. Timestamp and time range operations 6. Duration comparisons and utilities 7. Common durations (one_second, one_minute, etc.)

<!-- sdn-diagram:id=time_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=time_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

time_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=time_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 69 | 69 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Time Utilities Specification

This specification covers comprehensive time and duration utility functions: 1. Duration creation and manipulation (millis, seconds, minutes, hours, days) 2. Duration arithmetic (add, subtract, multiply, divide) 3. Duration parsing from strings (e.g., "1h30m45s") 4. Duration formatting and display 5. Timestamp and time range operations 6. Duration comparisons and utilities 7. Common durations (one_second, one_minute, etc.)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TIME-001 to #TIME-040 |
| Category | Tooling \| Time & Duration |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/time_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification covers comprehensive time and duration utility functions:
1. Duration creation and manipulation (millis, seconds, minutes, hours, days)
2. Duration arithmetic (add, subtract, multiply, divide)
3. Duration parsing from strings (e.g., "1h30m45s")
4. Duration formatting and display
5. Timestamp and time range operations
6. Duration comparisons and utilities
7. Common durations (one_second, one_minute, etc.)

## Key Concepts

| Concept | Description |
|---------|-------------|
| Duration | Immutable time span in milliseconds |
| Timestamp | Point in time (Unix epoch seconds) |
| Time Range | Span between two timestamps |
| Components | Break duration into days, hours, minutes, seconds, millis |
| Parsing | String to duration conversion (e.g., "1h30m") |
| Formatting | Duration to human-readable string |

## Behavior

- Duration stores milliseconds internally
- Timestamp represents Unix epoch seconds
- Duration parsing supports: d=days, h=hours, m=minutes, s=seconds
- Format output includes only non-zero components or 0s
- Time ranges are inclusive on both bounds
- Negative durations are allowed

## Scenarios

### Time Utilities

### Duration Creation

#### creates from millis

1. expect duration total millis


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_millis(5000)
expect duration.total_millis() == 5000
```

</details>

#### creates from seconds

1. expect duration total seconds
2. expect duration total millis


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(10)
expect duration.total_seconds() == 10
expect duration.total_millis() == 10000
```

</details>

#### creates from minutes

1. expect duration total minutes
2. expect duration total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_minutes(5)
expect duration.total_minutes() == 5
expect duration.total_seconds() == 300
```

</details>

#### creates from hours

1. expect duration total hours
2. expect duration total minutes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_hours(2)
expect duration.total_hours() == 2
expect duration.total_minutes() == 120
```

</details>

#### creates from days

1. expect duration total days
2. expect duration total hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_days(3)
expect duration.total_days() == 3
expect duration.total_hours() == 72
```

</details>

### Duration Components

#### extracts simple components

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(90)
val comps = duration.components()
expect comps.0 == 0
expect comps.1 == 0
expect comps.2 == 1
expect comps.3 == 30
expect comps.4 == 0
```

</details>

#### extracts complex components

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = (1 * 24 * 60 * 60 * 1000) + (2 * 60 * 60 * 1000) + (30 * 60 * 1000) + (45 * 1000)
val duration = Duration.from_millis(ms)
val comps = duration.components()
expect comps.0 == 1
expect comps.1 == 2
expect comps.2 == 30
expect comps.3 == 45
```

</details>

### Duration Arithmetic

#### adds durations

1. expect result total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d1 = Duration.from_seconds(30)
val d2 = Duration.from_seconds(15)
val result = d1.add(d2)
expect result.total_seconds() == 45
```

</details>

#### subtracts durations

1. expect result total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d1 = Duration.from_seconds(50)
val d2 = Duration.from_seconds(20)
val result = d1.subtract(d2)
expect result.total_seconds() == 30
```

</details>

#### multiplies duration

1. expect result total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(10)
val result = duration.multiply(3)
expect result.total_seconds() == 30
```

</details>

#### divides duration

1. expect result total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(60)
val result = duration.divide(4)
expect result.total_seconds() == 15
```

</details>

### Duration Parsing

#### parses seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_duration("45s"):
    case Some(duration): expect duration.total_seconds() == 45
    case nil: expect false
```

</details>

#### parses minutes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_duration("5m"):
    case Some(duration): expect duration.total_minutes() == 5
    case nil: expect false
```

</details>

#### parses hours

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_duration("2h"):
    case Some(duration): expect duration.total_hours() == 2
    case nil: expect false
```

</details>

#### parses days

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_duration("3d"):
    case Some(duration): expect duration.total_days() == 3
    case nil: expect false
```

</details>

#### parses combined duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_duration("1h30m"):
    case Some(duration): expect duration.total_minutes() == 90
    case nil: expect false
```

</details>

#### parses complex duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_duration("2d5h30m15s"):
    case Some(duration):
        val comps = duration.components()
        expect comps.0 == 2
        expect comps.1 == 5
        expect comps.2 == 30
        expect comps.3 == 15
    case nil: expect false
```

</details>

#### parses with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_duration("1h 30m"):
    case Some(duration): expect duration.total_minutes() == 90
    case nil: expect false
```

</details>

#### parses number only as seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_duration("30"):
    case Some(duration): expect duration.total_seconds() == 30
    case nil: expect false
```

</details>

#### returns nil for invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_duration("invalid"):
    case Some(_): expect false
    case nil: expect true
```

</details>

#### returns nil for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_duration(""):
    case Some(_): expect false
    case nil: expect true
```

</details>

### Duration Formatting

#### formats seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(45)
val formatted = format_duration(duration)
expect formatted == "45s"
```

</details>

#### formats minutes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_minutes(5)
val formatted = format_duration(duration)
expect formatted == "5m"
```

</details>

#### formats hours

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_hours(2)
val formatted = format_duration(duration)
expect formatted == "2h"
```

</details>

#### formats combined

1. expect formatted contains
2. expect formatted contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(90)
val formatted = format_duration(duration)
expect formatted.contains("1m")
expect formatted.contains("30s")
```

</details>

#### formats zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_millis(0)
val formatted = format_duration(duration)
expect formatted == "0s"
```

</details>

#### formats compact

1. expect formatted contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(90)
val formatted = format_duration_compact(duration)
expect formatted.contains("1m30s")
```

</details>

#### formats as seconds

1. expect formatted contains
2. expect formatted contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(123)
val formatted = format_as_seconds(duration)
expect formatted.contains("123")
expect formatted.contains("s")
```

</details>

#### formats as minutes

1. expect formatted contains
2. expect formatted contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(150)
val formatted = format_as_minutes(duration)
expect formatted.contains("2m")
expect formatted.contains("30s")
```

</details>

#### formats as hours

1. expect formatted contains
2. expect formatted contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_minutes(150)
val formatted = format_as_hours(duration)
expect formatted.contains("2h")
expect formatted.contains("30m")
```

</details>

### Time Unit Conversion

#### converts millis to seconds

1. expect millis to seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect millis_to_seconds(5000) == 5
```

</details>

#### converts seconds to millis

1. expect seconds to millis


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect seconds_to_millis(10) == 10000
```

</details>

#### converts minutes to seconds

1. expect minutes to seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect minutes_to_seconds(5) == 300
```

</details>

#### converts hours to minutes

1. expect hours to minutes


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect hours_to_minutes(2) == 120
```

</details>

#### converts days to hours

1. expect days to hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect days_to_hours(3) == 72
```

</details>

#### converts hours to seconds

1. expect hours to seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect hours_to_seconds(1) == 3600
```

</details>

#### converts days to seconds

1. expect days to seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect days_to_seconds(1) == 86400
```

</details>

### Timestamp

#### creates from seconds

1. expect ts get seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = Timestamp.from_seconds(1000000)
expect ts.get_seconds() == 1000000
```

</details>

#### adds duration

1. expect new ts get seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = Timestamp.from_seconds(1000)
val duration = Duration.from_seconds(500)
val new_ts = ts.add_duration(duration)
expect new_ts.get_seconds() == 1500
```

</details>

#### subtracts duration

1. expect new ts get seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = Timestamp.from_seconds(1000)
val duration = Duration.from_seconds(200)
val new_ts = ts.subtract_duration(duration)
expect new_ts.get_seconds() == 800
```

</details>

#### calculates duration since

1. expect duration total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts1 = Timestamp.from_seconds(2000)
val ts2 = Timestamp.from_seconds(1000)
val duration = ts1.duration_since(ts2)
expect duration.total_seconds() == 1000
```

</details>

#### handles boundary

1. expect ts get seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = Timestamp.from_seconds(0)
expect ts.get_seconds() == 0
```

</details>

### Duration Comparison

#### checks equality

1. expect duration equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d1 = Duration.from_seconds(60)
val d2 = Duration.from_minutes(1)
expect duration_equals(d1=d1, d2=d2)
```

</details>

#### checks greater than

1. expect duration greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d1 = Duration.from_seconds(100)
val d2 = Duration.from_seconds(50)
expect duration_greater_than(d1=d1, d2=d2)
```

</details>

#### checks less than

1. expect duration less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d1 = Duration.from_seconds(30)
val d2 = Duration.from_seconds(60)
expect duration_less_than(d1=d1, d2=d2)
```

</details>

#### finds max

1. expect max d total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d1 = Duration.from_seconds(100)
val d2 = Duration.from_seconds(50)
val max_d = duration_max(d1=d1, d2=d2)
expect max_d.total_seconds() == 100
```

</details>

#### finds min

1. expect min d total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d1 = Duration.from_seconds(100)
val d2 = Duration.from_seconds(50)
val min_d = duration_min(d1=d1, d2=d2)
expect min_d.total_seconds() == 50
```

</details>

### Common Durations

#### one_millisecond

1. expect duration total millis


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = one_millisecond()
expect duration.total_millis() == 1
```

</details>

#### one_second

1. expect duration total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = one_second()
expect duration.total_seconds() == 1
```

</details>

#### one_minute

1. expect duration total minutes


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = one_minute()
expect duration.total_minutes() == 1
```

</details>

#### one_hour

1. expect duration total hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = one_hour()
expect duration.total_hours() == 1
```

</details>

#### one_day

1. expect duration total days


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = one_day()
expect duration.total_days() == 1
```

</details>

### Duration Utilities

#### checks zero duration

1. expect is zero duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_millis(0)
expect is_zero_duration(duration)
```

</details>

#### checks negative duration

1. expect is negative duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_millis(-1000)
expect is_negative_duration(duration)
```

</details>

#### abs of positive

1. expect abs d total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(100)
val abs_d = duration_abs(duration)
expect abs_d.total_seconds() == 100
```

</details>

#### abs of negative

1. expect abs d total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_millis(-100000)
val abs_d = duration_abs(duration)
expect abs_d.total_seconds() == 100
```

</details>

#### negates duration

1. expect negated total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_seconds(100)
val negated = duration_negate(duration)
expect negated.total_seconds() == -100
```

</details>

#### sums durations

1. Duration from seconds
2. Duration from seconds
3. Duration from seconds
4. expect sum total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val durations = [
    Duration.from_seconds(10),
    Duration.from_seconds(20),
    Duration.from_seconds(30)
]
val sum = sum_durations(durations)
expect sum.total_seconds() == 60
```

</details>

#### sums empty list

1. expect sum total millis


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val durations: [Duration] = []
val sum = sum_durations(durations)
expect sum.total_millis() == 0
```

</details>

#### averages durations

1. Duration from seconds
2. Duration from seconds
3. Duration from seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val durations = [
    Duration.from_seconds(10),
    Duration.from_seconds(20),
    Duration.from_seconds(30)
]
match average_duration(durations):
    case Some(avg): expect avg.total_seconds() == 20
    case nil: expect false
```

</details>

#### average of empty returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val durations: [Duration] = []
match average_duration(durations):
    case Some(_): expect false
    case nil: expect true
```

</details>

### Time Range

#### calculates duration

1. expect duration total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = Timestamp.from_seconds(1000)
val end = Timestamp.from_seconds(2000)
val range = TimeRange.create(start=start, end=end)
val duration = range.duration()
expect duration.total_seconds() == 1000
```

</details>

#### contains timestamp

1. expect range contains
2. expect not range contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = Timestamp.from_seconds(1000)
val end = Timestamp.from_seconds(2000)
val range = TimeRange.create(start=start, end=end)
val ts_inside = Timestamp.from_seconds(1500)
expect range.contains(ts_inside)
val ts_outside = Timestamp.from_seconds(3000)
expect not range.contains(ts_outside)
```

</details>

#### detects overlap

1. start=Timestamp from seconds
2. end=Timestamp from seconds
3. start=Timestamp from seconds
4. end=Timestamp from seconds
5. expect range1 overlaps
6. expect range2 overlaps


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range1 = TimeRange.create(
    start=Timestamp.from_seconds(1000),
    end=Timestamp.from_seconds(2000)
)
val range2 = TimeRange.create(
    start=Timestamp.from_seconds(1500),
    end=Timestamp.from_seconds(2500)
)
expect range1.overlaps(range2)
expect range2.overlaps(range1)
```

</details>

#### detects no overlap

1. start=Timestamp from seconds
2. end=Timestamp from seconds
3. start=Timestamp from seconds
4. end=Timestamp from seconds
5. expect not range1 overlaps


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range1 = TimeRange.create(
    start=Timestamp.from_seconds(1000),
    end=Timestamp.from_seconds(2000)
)
val range2 = TimeRange.create(
    start=Timestamp.from_seconds(3000),
    end=Timestamp.from_seconds(4000)
)
expect not range1.overlaps(range2)
```

</details>

### Round-trip

#### parse and format simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "1h30m45s"
match parse_duration(original):
    case Some(duration):
        val formatted = format_duration_compact(duration)
        expect formatted == "1h30m45s"
    case nil: expect false
```

</details>

#### parse and format complex

1. expect formatted contains
2. expect formatted contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "2d5h"
match parse_duration(original):
    case Some(duration):
        val formatted = format_duration_compact(duration)
        expect formatted.contains("2d")
        expect formatted.contains("5h")
    case nil: expect false
```

</details>

### Edge Cases

#### handles very large duration

1. expect duration total days


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = Duration.from_days(365)
expect duration.total_days() == 365
```

</details>

#### handles zero operations

1. expect added total seconds
2. expect subtracted total seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = Duration.from_millis(0)
val d = Duration.from_seconds(100)
val added = d.add(zero)
expect added.total_seconds() == 100
val subtracted = d.subtract(zero)
expect subtracted.total_seconds() == 100
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 69 |
| Active scenarios | 69 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
