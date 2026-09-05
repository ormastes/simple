# Time Utils Specification

> Tests covering Time Utilities, Duration Creation, Duration Components, Duration Arithmetic, Duration Parsing, Duration Formatting, Time Unit Conversion, Timestamp, Duration Comparison, Common Durations, Duration Utilities, Time Range, Round-trip, Edge Cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 69 | 69 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Time Utils Specification

## Scenarios

### Time Utilities

### Duration Creation

#### creates from millis

- creates from millis


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates from millis")
val duration = Duration.from_millis(5000)
expect duration.total_millis() == 5000
```

</details>

#### creates from seconds

- creates from seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates from seconds")
val duration = Duration.from_seconds(10)
expect duration.total_seconds() == 10
expect duration.total_millis() == 10000
```

</details>

#### creates from minutes

- creates from minutes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates from minutes")
val duration = Duration.from_minutes(5)
expect duration.total_minutes() == 5
expect duration.total_seconds() == 300
```

</details>

#### creates from hours

- creates from hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates from hours")
val duration = Duration.from_hours(2)
expect duration.total_hours() == 2
expect duration.total_minutes() == 120
```

</details>

#### creates from days

- creates from days


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates from days")
val duration = Duration.from_days(3)
expect duration.total_days() == 3
expect duration.total_hours() == 72
```

</details>

### Duration Components

#### extracts simple components

- extracts simple components


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts simple components")
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

- extracts complex components


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts complex components")
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

- adds durations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds durations")
val d1 = Duration.from_seconds(30)
val d2 = Duration.from_seconds(15)
val result = d1.add(d2)
expect result.total_seconds() == 45
```

</details>

#### subtracts durations

- subtracts durations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subtracts durations")
val d1 = Duration.from_seconds(50)
val d2 = Duration.from_seconds(20)
val result = d1.subtract(d2)
expect result.total_seconds() == 30
```

</details>

#### multiplies duration

- multiplies duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiplies duration")
val duration = Duration.from_seconds(10)
val result = duration.multiply(3)
expect result.total_seconds() == 30
```

</details>

#### divides duration

- divides duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("divides duration")
val duration = Duration.from_seconds(60)
val result = duration.divide(4)
expect result.total_seconds() == 15
```

</details>

### Duration Parsing

#### parses seconds

- parses seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses seconds")
match parse_duration("45s"):
    case Some(duration): expect duration.total_seconds() == 45
    case nil: expect false
```

</details>

#### parses minutes

- parses minutes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses minutes")
match parse_duration("5m"):
    case Some(duration): expect duration.total_minutes() == 5
    case nil: expect false
```

</details>

#### parses hours

- parses hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hours")
match parse_duration("2h"):
    case Some(duration): expect duration.total_hours() == 2
    case nil: expect false
```

</details>

#### parses days

- parses days


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses days")
match parse_duration("3d"):
    case Some(duration): expect duration.total_days() == 3
    case nil: expect false
```

</details>

#### parses combined duration

- parses combined duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses combined duration")
match parse_duration("1h30m"):
    case Some(duration): expect duration.total_minutes() == 90
    case nil: expect false
```

</details>

#### parses complex duration

- parses complex duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses complex duration")
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

- parses with spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses with spaces")
match parse_duration("1h 30m"):
    case Some(duration): expect duration.total_minutes() == 90
    case nil: expect false
```

</details>

#### parses number only as seconds

- parses number only as seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses number only as seconds")
match parse_duration("30"):
    case Some(duration): expect duration.total_seconds() == 30
    case nil: expect false
```

</details>

#### returns nil for invalid

- returns nil for invalid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for invalid")
match parse_duration("invalid"):
    case Some(_): expect false
    case nil: expect true
```

</details>

#### returns nil for empty

- returns nil for empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for empty")
match parse_duration(""):
    case Some(_): expect false
    case nil: expect true
```

</details>

### Duration Formatting

#### formats seconds

- formats seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats seconds")
val duration = Duration.from_seconds(45)
val formatted = format_duration(duration)
expect formatted == "45s"
```

</details>

#### formats minutes

- formats minutes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats minutes")
val duration = Duration.from_minutes(5)
val formatted = format_duration(duration)
expect formatted == "5m"
```

</details>

#### formats hours

- formats hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats hours")
val duration = Duration.from_hours(2)
val formatted = format_duration(duration)
expect formatted == "2h"
```

</details>

#### formats combined

- formats combined


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats combined")
val duration = Duration.from_seconds(90)
val formatted = format_duration(duration)
expect formatted.contains("1m")
expect formatted.contains("30s")
```

</details>

#### formats zero

- formats zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats zero")
val duration = Duration.from_millis(0)
val formatted = format_duration(duration)
expect formatted == "0s"
```

</details>

#### formats compact

- formats compact


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats compact")
val duration = Duration.from_seconds(90)
val formatted = format_duration_compact(duration)
expect formatted.contains("1m30s")
```

</details>

#### formats as seconds

- formats as seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats as seconds")
val duration = Duration.from_seconds(123)
val formatted = format_as_seconds(duration)
expect formatted.contains("123")
expect formatted.contains("s")
```

</details>

#### formats as minutes

- formats as minutes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats as minutes")
val duration = Duration.from_seconds(150)
val formatted = format_as_minutes(duration)
expect formatted.contains("2m")
expect formatted.contains("30s")
```

</details>

#### formats as hours

- formats as hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats as hours")
val duration = Duration.from_minutes(150)
val formatted = format_as_hours(duration)
expect formatted.contains("2h")
expect formatted.contains("30m")
```

</details>

### Time Unit Conversion

#### converts millis to seconds

- converts millis to seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts millis to seconds")
expect millis_to_seconds(5000) == 5
```

</details>

#### converts seconds to millis

- converts seconds to millis


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts seconds to millis")
expect seconds_to_millis(10) == 10000
```

</details>

#### converts minutes to seconds

- converts minutes to seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts minutes to seconds")
expect minutes_to_seconds(5) == 300
```

</details>

#### converts hours to minutes

- converts hours to minutes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts hours to minutes")
expect hours_to_minutes(2) == 120
```

</details>

#### converts days to hours

- converts days to hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts days to hours")
expect days_to_hours(3) == 72
```

</details>

#### converts hours to seconds

- converts hours to seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts hours to seconds")
expect hours_to_seconds(1) == 3600
```

</details>

#### converts days to seconds

- converts days to seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts days to seconds")
expect days_to_seconds(1) == 86400
```

</details>

### Timestamp

#### creates from seconds

- creates from seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates from seconds")
val ts = Timestamp.from_seconds(1000000)
expect ts.get_seconds() == 1000000
```

</details>

#### adds duration

- adds duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds duration")
val ts = Timestamp.from_seconds(1000)
val duration = Duration.from_seconds(500)
val new_ts = ts.add_duration(duration)
expect new_ts.get_seconds() == 1500
```

</details>

#### subtracts duration

- subtracts duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subtracts duration")
val ts = Timestamp.from_seconds(1000)
val duration = Duration.from_seconds(200)
val new_ts = ts.subtract_duration(duration)
expect new_ts.get_seconds() == 800
```

</details>

#### calculates duration since

- calculates duration since


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates duration since")
val ts1 = Timestamp.from_seconds(2000)
val ts2 = Timestamp.from_seconds(1000)
val duration = ts1.duration_since(ts2)
expect duration.total_seconds() == 1000
```

</details>

#### handles boundary

- handles boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles boundary")
val ts = Timestamp.from_seconds(0)
expect ts.get_seconds() == 0
```

</details>

### Duration Comparison

#### checks equality

- checks equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks equality")
val d1 = Duration.from_seconds(60)
val d2 = Duration.from_minutes(1)
expect duration_equals(d1=d1, d2=d2)
```

</details>

#### checks greater than

- checks greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks greater than")
val d1 = Duration.from_seconds(100)
val d2 = Duration.from_seconds(50)
expect duration_greater_than(d1=d1, d2=d2)
```

</details>

#### checks less than

- checks less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks less than")
val d1 = Duration.from_seconds(30)
val d2 = Duration.from_seconds(60)
expect duration_less_than(d1=d1, d2=d2)
```

</details>

#### finds max

- finds max


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds max")
val d1 = Duration.from_seconds(100)
val d2 = Duration.from_seconds(50)
val max_d = duration_max(d1=d1, d2=d2)
expect max_d.total_seconds() == 100
```

</details>

#### finds min

- finds min


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds min")
val d1 = Duration.from_seconds(100)
val d2 = Duration.from_seconds(50)
val min_d = duration_min(d1=d1, d2=d2)
expect min_d.total_seconds() == 50
```

</details>

### Common Durations

#### one_millisecond

- one_millisecond


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one_millisecond")
val duration = one_millisecond()
expect duration.total_millis() == 1
```

</details>

#### one_second

- one_second


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one_second")
val duration = one_second()
expect duration.total_seconds() == 1
```

</details>

#### one_minute

- one_minute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one_minute")
val duration = one_minute()
expect duration.total_minutes() == 1
```

</details>

#### one_hour

- one_hour


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one_hour")
val duration = one_hour()
expect duration.total_hours() == 1
```

</details>

#### one_day

- one_day


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one_day")
val duration = one_day()
expect duration.total_days() == 1
```

</details>

### Duration Utilities

#### checks zero duration

- checks zero duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks zero duration")
val duration = Duration.from_millis(0)
expect is_zero_duration(duration)
```

</details>

#### checks negative duration

- checks negative duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks negative duration")
val duration = Duration.from_millis(-1000)
expect is_negative_duration(duration)
```

</details>

#### abs of positive

- abs of positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("abs of positive")
val duration = Duration.from_seconds(100)
val abs_d = duration_abs(duration)
expect abs_d.total_seconds() == 100
```

</details>

#### abs of negative

- abs of negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("abs of negative")
val duration = Duration.from_millis(-100000)
val abs_d = duration_abs(duration)
expect abs_d.total_seconds() == 100
```

</details>

#### negates duration

- negates duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negates duration")
val duration = Duration.from_seconds(100)
val negated = duration_negate(duration)
expect negated.total_seconds() == -100
```

</details>

#### sums durations

- sums durations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums durations")
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

- sums empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums empty list")
val durations: [Duration] = []
val sum = sum_durations(durations)
expect sum.total_millis() == 0
```

</details>

#### averages durations

- averages durations


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("averages durations")
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

- average of empty returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("average of empty returns nil")
val durations: [Duration] = []
match average_duration(durations):
    case Some(_): expect false
    case nil: expect true
```

</details>

### Time Range

#### calculates duration

- calculates duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates duration")
val start = Timestamp.from_seconds(1000)
val end = Timestamp.from_seconds(2000)
val range = TimeRange.create(start=start, end=end)
val duration = range.duration()
expect duration.total_seconds() == 1000
```

</details>

#### contains timestamp

- contains timestamp


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains timestamp")
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

- detects overlap


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects overlap")
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

- detects no overlap


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects no overlap")
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

- parse and format simple


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse and format simple")
val original = "1h30m45s"
match parse_duration(original):
    case Some(duration):
        val formatted = format_duration_compact(duration)
        expect formatted == "1h30m45s"
    case nil: expect false
```

</details>

#### parse and format complex

- parse and format complex


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse and format complex")
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

- handles very large duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles very large duration")
val duration = Duration.from_days(365)
expect duration.total_days() == 365
```

</details>

#### handles zero operations

- handles zero operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero operations")
val zero = Duration.from_millis(0)
val d = Duration.from_seconds(100)
val added = d.add(zero)
expect added.total_seconds() == 100
val subtracted = d.subtract(zero)
expect subtracted.total_seconds() == 100
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/time_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Time Utilities, Duration Creation, Duration Components, Duration Arithmetic, Duration Parsing, Duration Formatting, Time Unit Conversion, Timestamp, Duration Comparison, Common Durations, Duration Utilities, Time Range, Round-trip, Edge Cases.
- Time Utilities
- Duration Creation
- Duration Components
- Duration Arithmetic
- Duration Parsing
- Duration Formatting
- Time Unit Conversion
- Timestamp
- Duration Comparison
- Common Durations
- Duration Utilities
- Time Range
- Round-trip
- Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 69 |
| Active scenarios | 69 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6bd7ce5ffc2794f6791157015c418081398a49f2acd57c5e50ceff0b6079eb35`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6bd7ce5ffc2794f6791157015c418081398a49f2acd57c5e50ceff0b6079eb35`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6bd7ce5ffc2794f6791157015c418081398a49f2acd57c5e50ceff0b6079eb35`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/time_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/time_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/time_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/time_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/time_utils_spec.spl:358:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates from millis' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/time_utils_spec.spl:364:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates from seconds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/time_utils_spec.spl:371:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates from minutes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
