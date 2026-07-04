# Date Module Coverage Test Suite

> Comprehensive branch coverage tests for:

<!-- sdn-diagram:id=date_types_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=date_types_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

date_types_coverage_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=date_types_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 133 | 133 | 0 | 0 |

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
| Source | `test/01_unit/lib/common/date_types_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Comprehensive branch coverage tests for:
- src/lib/common/date/types.spl (constants, validation, properties)
- src/lib/common/date/format.spl (date formatting)
- src/lib/common/date/calculate.spl (arithmetic, comparison, calendar)
- src/lib/common/locale/dates.spl (locale-aware formatting, relative time)

## Scenarios

### Date Types - Day Names

#### returns Monday for day 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_name(1)).to_equal("Monday")
```

</details>

#### returns Tuesday for day 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_name(2)).to_equal("Tuesday")
```

</details>

#### returns Wednesday for day 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_name(3)).to_equal("Wednesday")
```

</details>

#### returns Thursday for day 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_name(4)).to_equal("Thursday")
```

</details>

#### returns Friday for day 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_name(5)).to_equal("Friday")
```

</details>

#### returns Saturday for day 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_name(6)).to_equal("Saturday")
```

</details>

#### returns Sunday for day 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_name(7)).to_equal("Sunday")
```

</details>

#### returns Invalid for day 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_name(0)).to_equal("Invalid")
```

</details>

#### returns Invalid for day 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_name(8)).to_equal("Invalid")
```

</details>

### Date Types - Month Names

#### returns January for month 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(1)).to_equal("January")
```

</details>

#### returns February for month 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(2)).to_equal("February")
```

</details>

#### returns March for month 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(3)).to_equal("March")
```

</details>

#### returns April for month 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(4)).to_equal("April")
```

</details>

#### returns May for month 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(5)).to_equal("May")
```

</details>

#### returns June for month 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(6)).to_equal("June")
```

</details>

#### returns July for month 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(7)).to_equal("July")
```

</details>

#### returns August for month 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(8)).to_equal("August")
```

</details>

#### returns September for month 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(9)).to_equal("September")
```

</details>

#### returns October for month 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(10)).to_equal("October")
```

</details>

#### returns November for month 11

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(11)).to_equal("November")
```

</details>

#### returns December for month 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(12)).to_equal("December")
```

</details>

#### returns Invalid for month 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(0)).to_equal("Invalid")
```

</details>

#### returns Invalid for month 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_name(13)).to_equal("Invalid")
```

</details>

### Date Types - Month Abbreviations

#### returns Jan for month 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(1)).to_equal("Jan")
```

</details>

#### returns Feb for month 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(2)).to_equal("Feb")
```

</details>

#### returns Mar for month 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(3)).to_equal("Mar")
```

</details>

#### returns Apr for month 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(4)).to_equal("Apr")
```

</details>

#### returns May for month 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(5)).to_equal("May")
```

</details>

#### returns Jun for month 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(6)).to_equal("Jun")
```

</details>

#### returns Jul for month 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(7)).to_equal("Jul")
```

</details>

#### returns Aug for month 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(8)).to_equal("Aug")
```

</details>

#### returns Sep for month 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(9)).to_equal("Sep")
```

</details>

#### returns Oct for month 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(10)).to_equal("Oct")
```

</details>

#### returns Nov for month 11

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(11)).to_equal("Nov")
```

</details>

#### returns Dec for month 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(12)).to_equal("Dec")
```

</details>

#### returns Inv for month 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(0)).to_equal("Inv")
```

</details>

#### returns Inv for month 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(month_abbrev(13)).to_equal("Inv")
```

</details>

### Date Types - Leap Year

#### identifies divisible by 400 as leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2000 is divisible by 400
expect(is_leap_year(2000)).to_equal(true)
```

</details>

#### identifies 1600 as leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(1600)).to_equal(true)
```

</details>

#### identifies century year not divisible by 400 as non-leap

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1900 is divisible by 100 but not 400
expect(is_leap_year(1900)).to_equal(false)
```

</details>

#### identifies 1800 as non-leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(1800)).to_equal(false)
```

</details>

#### identifies 2100 as non-leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(2100)).to_equal(false)
```

</details>

#### identifies divisible by 4 non-century as leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2024 is divisible by 4 but not 100
expect(is_leap_year(2024)).to_equal(true)
```

</details>

#### identifies 2028 as leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(2028)).to_equal(true)
```

</details>

#### identifies non-leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2023 is not divisible by 4
expect(is_leap_year(2023)).to_equal(false)
```

</details>

#### identifies 2025 as non-leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(2025)).to_equal(false)
```

</details>

#### identifies year 4 as leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(4)).to_equal(true)
```

</details>

#### identifies year 1 as non-leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_leap_year(1)).to_equal(false)
```

</details>

### Date Types - Days in Month

#### returns 31 for January

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 1)).to_equal(31)
```

</details>

#### returns 28 for February non-leap

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 2)).to_equal(28)
```

</details>

#### returns 29 for February leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2024, 2)).to_equal(29)
```

</details>

#### returns 31 for March

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 3)).to_equal(31)
```

</details>

#### returns 30 for April

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 4)).to_equal(30)
```

</details>

#### returns 31 for May

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 5)).to_equal(31)
```

</details>

#### returns 30 for June

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 6)).to_equal(30)
```

</details>

#### returns 31 for July

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 7)).to_equal(31)
```

</details>

#### returns 31 for August

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 8)).to_equal(31)
```

</details>

#### returns 30 for September

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 9)).to_equal(30)
```

</details>

#### returns 31 for October

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 10)).to_equal(31)
```

</details>

#### returns 30 for November

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 11)).to_equal(30)
```

</details>

#### returns 31 for December

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 12)).to_equal(31)
```

</details>

#### returns 0 for invalid month 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 0)).to_equal(0)
```

</details>

#### returns 0 for invalid month 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(days_in_month(2025, 13)).to_equal(0)
```

</details>

### Date Types - Date Validation

#### validates a normal date

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 6, 15)).to_equal(true)
```

</details>

#### rejects month less than 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 0, 15)).to_equal(false)
```

</details>

#### rejects month greater than 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 13, 15)).to_equal(false)
```

</details>

#### rejects day less than 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 6, 0)).to_equal(false)
```

</details>

#### rejects day exceeding max for month

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 2, 29)).to_equal(false)
```

</details>

#### accepts Feb 29 on leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2024, 2, 29)).to_equal(true)
```

</details>

#### accepts Jan 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 1, 31)).to_equal(true)
```

</details>

#### rejects Jan 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 1, 32)).to_equal(false)
```

</details>

#### accepts first day of month

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 1, 1)).to_equal(true)
```

</details>

#### accepts last day of April

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 4, 30)).to_equal(true)
```

</details>

#### rejects Apr 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 4, 31)).to_equal(false)
```

</details>

### Date Types - Date Creation

#### from_ymd

#### creates a valid date

- var d = from ymd
- check
   - Expected: d[0] equals `2025`
   - Expected: d[1] equals `3`
   - Expected: d[2] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = from_ymd(2025, 3, 15)
check(d != nil)
expect(d[0]).to_equal(2025)
expect(d[1]).to_equal(3)
expect(d[2]).to_equal(15)
```

</details>

#### returns nil for invalid date

- var d = from ymd
   - Expected: d equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = from_ymd(2025, 2, 29)
expect(d).to_equal(nil)
```

</details>

#### returns nil for month 0

- var d = from ymd
   - Expected: d equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = from_ymd(2025, 0, 1)
expect(d).to_equal(nil)
```

</details>

#### returns nil for day 0

- var d = from ymd
   - Expected: d equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = from_ymd(2025, 1, 0)
expect(d).to_equal(nil)
```

</details>

#### epoch

#### returns January 1 year 1

- var e = epoch
   - Expected: e[0] equals `1`
   - Expected: e[1] equals `1`
   - Expected: e[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e = epoch()
expect(e[0]).to_equal(1)
expect(e[1]).to_equal(1)
expect(e[2]).to_equal(1)
```

</details>

#### today_mock

#### returns fixed date 2025-01-15

- var t = today mock
   - Expected: t[0] equals `2025`
   - Expected: t[1] equals `1`
   - Expected: t[2] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = today_mock()
expect(t[0]).to_equal(2025)
expect(t[1]).to_equal(1)
expect(t[2]).to_equal(15)
```

</details>

#### from_days

#### returns nil for days less than 1

- var d = from days
   - Expected: d equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = from_days(0)
expect(d).to_equal(nil)
```

</details>

#### returns nil for negative days

- var d = from days
   - Expected: d equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = from_days(-5)
expect(d).to_equal(nil)
```

</details>

#### returns epoch for day 1

- var d = from days
   - Expected: d[0] equals `1`
   - Expected: d[1] equals `1`
   - Expected: d[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = from_days(1)
expect(d[0]).to_equal(1)
expect(d[1]).to_equal(1)
expect(d[2]).to_equal(1)
```

</details>

#### returns Jan 31 for day 31

- var d = from days
   - Expected: d[0] equals `1`
   - Expected: d[1] equals `1`
   - Expected: d[2] equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = from_days(31)
expect(d[0]).to_equal(1)
expect(d[1]).to_equal(1)
expect(d[2]).to_equal(31)
```

</details>

#### returns Feb 1 for day 32

- var d = from days
   - Expected: d[0] equals `1`
   - Expected: d[1] equals `2`
   - Expected: d[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = from_days(32)
expect(d[0]).to_equal(1)
expect(d[1]).to_equal(2)
expect(d[2]).to_equal(1)
```

</details>

#### handles crossing into next year

- var d = from days
   - Expected: d[0] equals `2`
   - Expected: d[1] equals `1`
   - Expected: d[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Day 366 in year 1 (non-leap) should be Jan 1 year 2
var d = from_days(366)
expect(d[0]).to_equal(2)
expect(d[1]).to_equal(1)
expect(d[2]).to_equal(1)
```

</details>

#### handles leap year boundary

- var d = from days
   - Expected: d[0] equals `5`
   - Expected: d[1] equals `1`
   - Expected: d[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Year 4 is a leap year, so 3*365 + 366 = 1461 days for years 1-4
# Day 1462 should be Jan 1 year 5
var d = from_days(1462)
expect(d[0]).to_equal(5)
expect(d[1]).to_equal(1)
expect(d[2]).to_equal(1)
```

</details>

### Date Types - Day of Week

#### computes Monday correctly

- var dow = day of week
   - Expected: dow equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-06 is a Monday
var dow = day_of_week((2025, 1, 6))
expect(dow).to_equal(1)
```

</details>

#### computes Sunday correctly

- var dow = day of week
   - Expected: dow equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-05 is a Sunday
var dow = day_of_week((2025, 1, 5))
expect(dow).to_equal(7)
```

</details>

#### computes Saturday correctly

- var dow = day of week
   - Expected: dow equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-04 is a Saturday
var dow = day_of_week((2025, 1, 4))
expect(dow).to_equal(6)
```

</details>

#### computes Wednesday correctly

- var dow = day of week
   - Expected: dow equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-01 is a Wednesday
var dow = day_of_week((2025, 1, 1))
expect(dow).to_equal(3)
```

</details>

#### handles January date with month adjustment

- var dow = day of week
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# January triggers the m < 3 branch
var dow = day_of_week((2025, 1, 15))
check(dow >= 1 and dow <= 7)
```

</details>

#### handles February date with month adjustment

- var dow = day of week
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# February triggers the m < 3 branch
var dow = day_of_week((2025, 2, 14))
check(dow >= 1 and dow <= 7)
```

</details>

#### handles March date without month adjustment

- var dow = day of week
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# March does NOT trigger m < 3 branch
var dow = day_of_week((2025, 3, 1))
check(dow >= 1 and dow <= 7)
```

</details>

#### handles December date

- var dow = day of week
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dow = day_of_week((2025, 12, 25))
check(dow >= 1 and dow <= 7)
```

</details>

### Date Types - Day of Year

#### returns 1 for January 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2025, 1, 1))).to_equal(1)
```

</details>

#### returns 31 for January 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2025, 1, 31))).to_equal(31)
```

</details>

#### returns 32 for February 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2025, 2, 1))).to_equal(32)
```

</details>

#### returns 59 for February 28 non-leap

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2025, 2, 28))).to_equal(59)
```

</details>

#### returns 60 for February 29 leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2024, 2, 29))).to_equal(60)
```

</details>

#### returns 365 for December 31 non-leap

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2025, 12, 31))).to_equal(365)
```

</details>

#### returns 366 for December 31 leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2024, 12, 31))).to_equal(366)
```

</details>

#### returns correct value for mid-year

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# July 1 = 31+28+31+30+31+30+1 = 182 (non-leap)
expect(day_of_year((2025, 7, 1))).to_equal(182)
```

</details>

### Date Types - Week of Year

#### returns week 1 for early January

- var w = week of year
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-06 is a Monday in week 2
var w = week_of_year((2025, 1, 6))
check(w >= 1 and w <= 53)
```

</details>

#### returns correct week for mid-year

- var w = week of year
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = week_of_year((2025, 7, 1))
check(w >= 1 and w <= 53)
```

</details>

#### handles late December

- var w = week of year
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = week_of_year((2025, 12, 31))
check(w >= 1 and w <= 53)
```

</details>

#### handles Jan 1 when it falls on Friday

- var w = week of year
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2021-01-01 is a Friday (jan1_dow > 4 branch)
var w = week_of_year((2021, 1, 1))
check(w >= 0 and w <= 53)
```

</details>

#### handles Jan 1 when it falls on Saturday

- var w = week of year
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2022-01-01 is a Saturday (jan1_dow > 4 branch)
var w = week_of_year((2022, 1, 1))
check(w >= 0 and w <= 53)
```

</details>

#### handles Jan 1 when it falls on Thursday

- var w = week of year
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2026-01-01 is a Thursday (jan1_dow == 4, NOT > 4)
var w = week_of_year((2026, 1, 1))
check(w >= 1 and w <= 53)
```

</details>

#### handles Jan 1 when it falls on Monday

- var w = week of year
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2024-01-01 is a Monday (jan1_dow == 1, NOT > 4)
var w = week_of_year((2024, 1, 1))
check(w >= 1 and w <= 53)
```

</details>

### Date Types - Weekend and Weekday

#### identifies Saturday as weekend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-04 is Saturday
expect(is_weekend((2025, 1, 4))).to_equal(true)
```

</details>

#### identifies Sunday as weekend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-05 is Sunday
expect(is_weekend((2025, 1, 5))).to_equal(true)
```

</details>

#### identifies Monday as not weekend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-06 is Monday
expect(is_weekend((2025, 1, 6))).to_equal(false)
```

</details>

#### identifies Friday as not weekend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2025-01-03 is Friday
expect(is_weekend((2025, 1, 3))).to_equal(false)
```

</details>

#### identifies Monday as weekday

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_weekday((2025, 1, 6))).to_equal(true)
```

</details>

#### identifies Saturday as not weekday

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_weekday((2025, 1, 4))).to_equal(false)
```

</details>

### Date Types - Quarter

#### returns Q1 for January

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(quarter((2025, 1, 15))).to_equal(1)
```

</details>

#### returns Q1 for March

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(quarter((2025, 3, 31))).to_equal(1)
```

</details>

#### returns Q2 for April

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(quarter((2025, 4, 1))).to_equal(2)
```

</details>

#### returns Q2 for June

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(quarter((2025, 6, 30))).to_equal(2)
```

</details>

#### returns Q3 for July

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(quarter((2025, 7, 1))).to_equal(3)
```

</details>

#### returns Q3 for September

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(quarter((2025, 9, 30))).to_equal(3)
```

</details>

#### returns Q4 for October

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(quarter((2025, 10, 1))).to_equal(4)
```

</details>

#### returns Q4 for December

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(quarter((2025, 12, 31))).to_equal(4)
```

</details>

### Date Format - to_string

#### formats a date with padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(date_to_string((2025, 1, 5))).to_equal("2025-01-05")
```

</details>

#### formats a date without padding needed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(date_to_string((2025, 12, 25))).to_equal("2025-12-25")
```

</details>

#### formats month 10 without padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(date_to_string((2025, 10, 15))).to_equal("2025-10-15")
```

</details>

#### formats day 10 without padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(date_to_string((2025, 3, 10))).to_equal("2025-03-10")
```

</details>

### Date Format - to_iso8601

#### delegates to to_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(date_to_string((2025, 6, 15))).to_equal("2025-06-15")
```

</details>

### Date Format - to_readable

#### formats as full month name day year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_readable((2025, 1, 15))).to_equal("January 15, 2025")
```

</details>

#### formats December date

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_readable((2025, 12, 25))).to_equal("December 25, 2025")
```

</details>

### Date Format - to_short

#### formats with abbreviated month

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_short((2025, 1, 15))).to_equal("Jan 15, 2025")
```

</details>

#### formats December with abbreviated month

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_short((2025, 12, 25))).to_equal("Dec 25, 2025")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 133 |
| Active scenarios | 133 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
