# Date Module Coverage Test Suite

> Comprehensive branch coverage tests for:

<!-- sdn-diagram:id=date_calculate_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=date_calculate_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

date_calculate_coverage_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=date_calculate_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Date Module Coverage Test Suite

Comprehensive branch coverage tests for:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DATE_COVERAGE |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/lib/common/date_calculate_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Comprehensive branch coverage tests for:
- src/lib/common/date/types.spl (constants, validation, properties)
- src/lib/common/date/format.spl (date formatting)
- src/lib/common/date/calculate.spl (arithmetic, comparison, calendar)
- src/lib/common/locale/dates.spl (locale-aware formatting, relative time)

## Scenarios

### Date Calculate - Last Day of Week in Month

#### finds last Monday of May 2025

1. var result = last day of week in month
2. check
   - Expected: result[1] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = last_day_of_week_in_month((2025, 5, 1), 1)
check(result != nil)
expect(result[1]).to_equal(5)
expect(result[2]).to_be_greater_than(24)
```

</details>

#### finds last Friday of January 2025

1. var result = last day of week in month
2. check
   - Expected: result[2] equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = last_day_of_week_in_month((2025, 1, 1), 5)
check(result != nil)
expect(result[2]).to_equal(31)
```

</details>

### Date Calculate - Next and Previous Day of Week

#### finds next Monday from Wednesday

1. var result = next day of week
   - Expected: result[2] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-01 is Wednesday, next Monday is Jan 6
var result = next_day_of_week((2025, 1, 1), 1)
expect(result[2]).to_equal(6)
```

</details>

#### finds next day when already on that day

1. var result = next day of week
   - Expected: result[2] equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-06 is Monday, next Monday should be Jan 13
var result = next_day_of_week((2025, 1, 6), 1)
expect(result[2]).to_equal(13)
```

</details>

#### finds previous Friday from Wednesday

1. var result = prev day of week
   - Expected: result[1] equals `12`
   - Expected: result[2] equals `27`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-01 is Wednesday, previous Friday is Dec 27
var result = prev_day_of_week((2025, 1, 1), 5)
expect(result[1]).to_equal(12)
expect(result[2]).to_equal(27)
```

</details>

#### finds previous day when already on that day

1. var result = prev day of week
   - Expected: result[0] equals `2024`
   - Expected: result[1] equals `12`
   - Expected: result[2] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-06 is Monday, prev Monday should be Dec 30
var result = prev_day_of_week((2025, 1, 6), 1)
expect(result[0]).to_equal(2024)
expect(result[1]).to_equal(12)
expect(result[2]).to_equal(30)
```

</details>

### Date Calculate - Days Between

#### counts inclusive days

1. var count = days between
   - Expected: count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = days_between((2025, 1, 1), (2025, 1, 5))
expect(count).to_equal(5)
```

</details>

#### returns 1 for same date

1. var count = days between
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = days_between((2025, 1, 1), (2025, 1, 1))
expect(count).to_equal(1)
```

</details>

### Date Calculate - Weekdays and Weekends Between

#### counts weekdays in a full week

1. var count = weekdays between
   - Expected: count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Mon Jan 6 to Sun Jan 12 = 5 weekdays
var count = weekdays_between((2025, 1, 6), (2025, 1, 12))
expect(count).to_equal(5)
```

</details>

#### counts weekends in a full week

1. var count = weekends between
   - Expected: count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = weekends_between((2025, 1, 6), (2025, 1, 12))
expect(count).to_equal(2)
```

</details>

### Date Calculate - Count Specific Day of Week

#### counts Mondays in January 2025

1. var count = count day of week
   - Expected: count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Jan 2025 has Mondays on 6, 13, 20, 27
var count = count_day_of_week((2025, 1, 1), (2025, 1, 31), 1)
expect(count).to_equal(4)
```

</details>

### Date Calculate - Easter and Holidays

#### calculates Easter 2025

1. var result = easter date
2. check
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `4`
   - Expected: result[2] equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = easter_date(2025)
check(result != nil)
# Easter 2025 is April 20
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(4)
expect(result[2]).to_equal(20)
```

</details>

#### returns nil for year before 1583

1. var result = easter date
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = easter_date(1582)
expect(result).to_equal(nil)
```

</details>

#### calculates Good Friday 2025

1. var result = good friday
2. check
   - Expected: result[1] equals `4`
   - Expected: result[2] equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = good_friday(2025)
check(result != nil)
expect(result[1]).to_equal(4)
expect(result[2]).to_equal(18)
```

</details>

#### returns nil for Good Friday before 1583

1. var result = good friday
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = good_friday(1582)
expect(result).to_equal(nil)
```

</details>

#### calculates Ash Wednesday 2025

1. var result = ash wednesday
2. check
   - Expected: result[1] equals `3`
   - Expected: result[2] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ash_wednesday(2025)
check(result != nil)
# 46 days before Easter Apr 20 = March 5
expect(result[1]).to_equal(3)
expect(result[2]).to_equal(5)
```

</details>

#### returns nil for Ash Wednesday before 1583

1. var result = ash wednesday
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ash_wednesday(1582)
expect(result).to_equal(nil)
```

</details>

#### calculates Pentecost 2025

1. var result = pentecost
2. check
   - Expected: result[1] equals `6`
   - Expected: result[2] equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = pentecost(2025)
check(result != nil)
# 49 days after Easter Apr 20 = June 8
expect(result[1]).to_equal(6)
expect(result[2]).to_equal(8)
```

</details>

#### returns nil for Pentecost before 1583

1. var result = pentecost
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = pentecost(1582)
expect(result).to_equal(nil)
```

</details>

#### calculates Thanksgiving US 2025

1. var result = thanksgiving us
2. check
   - Expected: result[1] equals `11`
   - Expected: result[2] equals `27`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = thanksgiving_us(2025)
check(result != nil)
expect(result[1]).to_equal(11)
# 4th Thursday of Nov 2025 is Nov 27
expect(result[2]).to_equal(27)
```

</details>

#### calculates Labor Day US 2025

1. var result = labor day us
2. check
   - Expected: result[1] equals `9`
   - Expected: result[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = labor_day_us(2025)
check(result != nil)
expect(result[1]).to_equal(9)
# 1st Monday of Sep 2025 is Sep 1
expect(result[2]).to_equal(1)
```

</details>

#### calculates Memorial Day US 2025

1. var result = memorial day us
2. check
   - Expected: result[1] equals `5`
   - Expected: result[2] equals `26`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = memorial_day_us(2025)
check(result != nil)
expect(result[1]).to_equal(5)
# Last Monday of May 2025 is May 26
expect(result[2]).to_equal(26)
```

</details>

### Date Calculate - Age and Duration

#### age_in_years

#### calculates age when birthday has passed

1. var age = age in years
   - Expected: age equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var age = age_in_years((1990, 3, 15), (2025, 6, 15))
expect(age).to_equal(35)
```

</details>

#### calculates age when birthday has not passed

1. var age = age in years
   - Expected: age equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var age = age_in_years((1990, 8, 15), (2025, 6, 15))
expect(age).to_equal(34)
```

</details>

#### calculates age on birthday month but day not yet

1. var age = age in years
   - Expected: age equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var age = age_in_years((1990, 6, 20), (2025, 6, 15))
expect(age).to_equal(34)
```

</details>

#### calculates age on exact birthday

1. var age = age in years
   - Expected: age equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var age = age_in_years((1990, 6, 15), (2025, 6, 15))
expect(age).to_equal(35)
```

</details>

#### difference_in_months

#### returns positive months for later date first

1. var months = difference in months
   - Expected: months equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var months = difference_in_months((2025, 6, 15), (2025, 1, 15))
expect(months).to_equal(5)
```

</details>

#### adjusts when day1 less than day2

1. var months = difference in months
   - Expected: months equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var months = difference_in_months((2025, 6, 10), (2025, 1, 15))
expect(months).to_equal(4)
```

</details>

#### returns zero for same date

1. var months = difference in months
   - Expected: months equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var months = difference_in_months((2025, 1, 15), (2025, 1, 15))
expect(months).to_equal(0)
```

</details>

#### difference_in_years

#### returns years between dates

1. var years = difference in years
   - Expected: years equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var years = difference_in_years((2025, 6, 15), (2020, 6, 15))
expect(years).to_equal(5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
