# Time Utils Specification

> <details>

<!-- sdn-diagram:id=time_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=time_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

time_utils_spec -> std
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
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Time Utils Specification

## Scenarios

### time_utils — pure arithmetic civil-date library

#### is_leap_year

#### 2000 is a leap year (divisible by 400)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(2000)).to_equal(true)
```

</details>

#### 1900 is not a leap year (divisible by 100 but not 400)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(1900)).to_equal(false)
```

</details>

#### 2024 is a leap year (divisible by 4 not 100)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(2024)).to_equal(true)
```

</details>

#### 2023 is not a leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(2023)).to_equal(false)
```

</details>

#### 1 AD is not a leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(1)).to_equal(false)
```

</details>

#### days_in_month

#### January has 31 days

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2024, 1)).to_equal(31)
```

</details>

#### April has 30 days

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2024, 4)).to_equal(30)
```

</details>

#### February 2024 has 29 days (leap year)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2024, 2)).to_equal(29)
```

</details>

#### February 2023 has 28 days (non-leap)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2023, 2)).to_equal(28)
```

</details>

#### February 1900 has 28 days (century not divisible by 400)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(1900, 2)).to_equal(28)
```

</details>

#### February 2000 has 29 days (400-year leap)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2000, 2)).to_equal(29)
```

</details>

#### December has 31 days

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2024, 12)).to_equal(31)
```

</details>

#### timestamp_get_year

#### epoch (micros=0) is year 1970

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_year(0)).to_equal(1970)
```

</details>

#### 2000-01-01 00:00:00 UTC is year 2000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 946684800 seconds * 1_000_000
expect(timestamp_get_year(946684800000000)).to_equal(2000)
```

</details>

#### one second before epoch is year 1969

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_year(-1000000)).to_equal(1969)
```

</details>

#### 2024-02-29 is year 2024

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2024-02-29 00:00:00 UTC = 1709164800 seconds
expect(timestamp_get_year(1709164800000000)).to_equal(2024)
```

</details>

#### timestamp_get_month

#### epoch (micros=0) is month 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_month(0)).to_equal(1)
```

</details>

#### 2000-01-01 is month 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_month(946684800000000)).to_equal(1)
```

</details>

#### one second before epoch is month 12 (December 1969)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_month(-1000000)).to_equal(12)
```

</details>

#### 2024-02-29 is month 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_month(1709164800000000)).to_equal(2)
```

</details>

#### timestamp_get_day

#### epoch (micros=0) is day 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_day(0)).to_equal(1)
```

</details>

#### 2000-01-01 is day 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_day(946684800000000)).to_equal(1)
```

</details>

#### one second before epoch is day 31 (1969-12-31)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_day(-1000000)).to_equal(31)
```

</details>

#### 2024-02-29 is day 29

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_day(1709164800000000)).to_equal(29)
```

</details>

#### timestamp_get_hour

#### epoch is hour 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_hour(0)).to_equal(0)
```

</details>

#### 3600 seconds past epoch is hour 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_hour(3600000000)).to_equal(1)
```

</details>

#### one second before epoch is hour 23

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_hour(-1000000)).to_equal(23)
```

</details>

#### timestamp_get_minute

#### epoch is minute 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_minute(0)).to_equal(0)
```

</details>

#### 1830 seconds past epoch is minute 30

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 30 * 60 + 30 = 1830 seconds = 30m30s → minute 30
expect(timestamp_get_minute(1830000000)).to_equal(30)
```

</details>

#### one second before epoch is minute 59

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_minute(-1000000)).to_equal(59)
```

</details>

#### timestamp_get_second

#### epoch is second 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_second(0)).to_equal(0)
```

</details>

#### 45 seconds past epoch is second 45

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_second(45000000)).to_equal(45)
```

</details>

#### one second before epoch is second 59

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_second(-1000000)).to_equal(59)
```

</details>

#### timestamp_get_microsecond

#### epoch has 0 microseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_microsecond(0)).to_equal(0)
```

</details>

#### 500000 micros past epoch is 500000 sub-second micros

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_microsecond(500000)).to_equal(500000)
```

</details>

#### one microsecond before epoch is 999999

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_get_microsecond(-1)).to_equal(999999)
```

</details>

#### day_of_week

#### epoch 1970-01-01 is Thursday (4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_week(0)).to_equal(4)
```

</details>

#### 1970-01-04 is Sunday (0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 3 days after epoch
expect(day_of_week(3 * 86400000000)).to_equal(0)
```

</details>

#### 2000-01-01 is Saturday (6)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_week(946684800000000)).to_equal(6)
```

</details>

#### one day before epoch 1969-12-31 is Wednesday (3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_week(-86400000000)).to_equal(3)
```

</details>

#### timestamp_from_components

#### Unix epoch from components

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_from_components(1970, 1, 1, 0, 0, 0, 0)).to_equal(0)
```

</details>

#### 2000-01-01 00:00:00 from components

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_from_components(2000, 1, 1, 0, 0, 0, 0)).to_equal(946684800000000)
```

</details>

#### one second before epoch from components

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_from_components(1969, 12, 31, 23, 59, 59, 0)).to_equal(-1000000)
```

</details>

#### 2024-02-29 from components

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_from_components(2024, 2, 29, 0, 0, 0, 0)).to_equal(1709164800000000)
```

</details>

#### round-trip: from_components then get_*

#### round-trips 2023-07-15 14:30:45.123456

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = timestamp_from_components(2023, 7, 15, 14, 30, 45, 123456)
expect(timestamp_get_year(micros)).to_equal(2023)
expect(timestamp_get_month(micros)).to_equal(7)
expect(timestamp_get_day(micros)).to_equal(15)
expect(timestamp_get_hour(micros)).to_equal(14)
expect(timestamp_get_minute(micros)).to_equal(30)
expect(timestamp_get_second(micros)).to_equal(45)
expect(timestamp_get_microsecond(micros)).to_equal(123456)
```

</details>

#### round-trips 1800-03-01 (pre-1970 distant past)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = timestamp_from_components(1800, 3, 1, 0, 0, 0, 0)
expect(timestamp_get_year(micros)).to_equal(1800)
expect(timestamp_get_month(micros)).to_equal(3)
expect(timestamp_get_day(micros)).to_equal(1)
```

</details>

#### timestamp_add_days

#### adding 0 days is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_add_days(0, 0)).to_equal(0)
```

</details>

#### adding 1 day to epoch gives 86400000000 micros

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_add_days(0, 1)).to_equal(86400000000)
```

</details>

#### adding negative days moves backward

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_add_days(86400000000, -1)).to_equal(0)
```

</details>

#### timestamp_diff_days

#### same timestamp gives 0 days difference

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_diff_days(0, 0)).to_equal(0)
```

</details>

#### one day apart gives 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_diff_days(86400000000, 0)).to_equal(1)
```

</details>

#### reversed gives -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(timestamp_diff_days(0, 86400000000)).to_equal(-1)
```

</details>

#### 365 days apart

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val one_year = 365 * 86400000000
expect(timestamp_diff_days(one_year, 0)).to_equal(365)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/time_utils/time_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- time_utils — pure arithmetic civil-date library

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
