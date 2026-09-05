# Date Module Coverage Test Suite

> Comprehensive branch coverage tests for:

<!-- sdn-diagram:id=date_format_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=date_format_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

date_format_coverage_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=date_format_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 65 | 65 | 0 | 0 |

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
| Source | `test/01_unit/lib/common/date_format_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Comprehensive branch coverage tests for:
- src/lib/common/date/types.spl (constants, validation, properties)
- src/lib/common/date/format.spl (date formatting)
- src/lib/common/date/calculate.spl (arithmetic, comparison, calendar)
- src/lib/common/locale/dates.spl (locale-aware formatting, relative time)

## Scenarios

### Date Format - text_from_i64 helper

#### converts zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(0)).to_equal("0")
```

</details>

#### converts positive number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(42)).to_equal("42")
```

</details>

#### converts negative number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(-7)).to_equal("-7")
```

</details>

#### converts single digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(5)).to_equal("5")
```

</details>

#### converts large number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(2025)).to_equal("2025")
```

</details>

### Date Calculate - to_days

#### converts epoch to day 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_days((1, 1, 1))).to_equal(1)
```

</details>

#### converts Jan 31 year 1 to day 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_days((1, 1, 31))).to_equal(31)
```

</details>

#### converts Feb 1 year 1 to day 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_days((1, 2, 1))).to_equal(32)
```

</details>

#### handles year crossing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Year 1 has 365 days, so Jan 1 year 2 = day 366
expect(to_days((2, 1, 1))).to_equal(366)
```

</details>

#### handles leap year in calculation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Year 4 is leap: days = 365*3 + 366 + 1 = 1462
expect(to_days((5, 1, 1))).to_equal(1462)
```

</details>

### Date Calculate - add_days

#### adds days to a date

- var result = add days
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `1`
   - Expected: result[2] equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_days((2025, 1, 1), 10)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(11)
```

</details>

#### adds days crossing month boundary

- var result = add days
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `2`
   - Expected: result[2] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_days((2025, 1, 30), 5)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(4)
```

</details>

#### returns nil when result is before epoch

- var result = add days
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_days((1, 1, 1), -5)
expect(result).to_equal(nil)
```

</details>

### Date Calculate - subtract_days

#### subtracts days from a date

- var result = subtract days
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `1`
   - Expected: result[2] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = subtract_days((2025, 1, 15), 5)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(10)
```

</details>

### Date Calculate - difference_in_days

#### returns positive for later date first

- var diff = difference in days
   - Expected: diff equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diff = difference_in_days((2025, 1, 15), (2025, 1, 10))
expect(diff).to_equal(5)
```

</details>

#### returns negative for earlier date first

- var diff = difference in days
   - Expected: diff equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diff = difference_in_days((2025, 1, 10), (2025, 1, 15))
expect(diff).to_equal(-5)
```

</details>

#### returns zero for same date

- var diff = difference in days
   - Expected: diff equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var diff = difference_in_days((2025, 1, 15), (2025, 1, 15))
expect(diff).to_equal(0)
```

</details>

### Date Calculate - add_months

#### adds months within same year

- var result = add months
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `4`
   - Expected: result[2] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_months((2025, 1, 15), 3)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(4)
expect(result[2]).to_equal(15)
```

</details>

#### adds months crossing year boundary

- var result = add months
   - Expected: result[0] equals `2026`
   - Expected: result[1] equals `2`
   - Expected: result[2] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_months((2025, 11, 15), 3)
expect(result[0]).to_equal(2026)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(15)
```

</details>

#### clamps day when new month has fewer days

- var result = add months
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `2`
   - Expected: result[2] equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Jan 31 + 1 month -> Feb 28 (2025 non-leap)
var result = add_months((2025, 1, 31), 1)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(28)
```

</details>

#### handles negative months

- var result = add months
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `1`
   - Expected: result[2] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_months((2025, 3, 15), -2)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(15)
```

</details>

#### handles negative months crossing year boundary

- var result = add months
   - Expected: result[0] equals `2024`
   - Expected: result[1] equals `11`
   - Expected: result[2] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_months((2025, 2, 15), -3)
expect(result[0]).to_equal(2024)
expect(result[1]).to_equal(11)
expect(result[2]).to_equal(15)
```

</details>

### Date Calculate - subtract_months

#### subtracts months

- var result = subtract months
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `3`
   - Expected: result[2] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = subtract_months((2025, 6, 15), 3)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(3)
expect(result[2]).to_equal(15)
```

</details>

### Date Calculate - add_years

#### adds years to a normal date

- var result = add years
   - Expected: result[0] equals `2027`
   - Expected: result[1] equals `6`
   - Expected: result[2] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_years((2025, 6, 15), 2)
expect(result[0]).to_equal(2027)
expect(result[1]).to_equal(6)
expect(result[2]).to_equal(15)
```

</details>

#### handles Feb 29 landing on non-leap year

- var result = add years
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `2`
   - Expected: result[2] equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2024 is leap, 2025 is not
var result = add_years((2024, 2, 29), 1)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(28)
```

</details>

#### handles Feb 29 landing on leap year

- var result = add years
   - Expected: result[0] equals `2028`
   - Expected: result[1] equals `2`
   - Expected: result[2] equals `29`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2024 is leap, 2028 is also leap
var result = add_years((2024, 2, 29), 4)
expect(result[0]).to_equal(2028)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(29)
```

</details>

#### does not adjust non-Feb dates

- var result = add years
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `3`
   - Expected: result[2] equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_years((2024, 3, 15), 1)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(3)
expect(result[2]).to_equal(15)
```

</details>

#### does not adjust Feb 28

- var result = add years
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `2`
   - Expected: result[2] equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_years((2024, 2, 28), 1)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(28)
```

</details>

### Date Calculate - subtract_years

#### subtracts years

- var result = subtract years
   - Expected: result[0] equals `2020`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = subtract_years((2025, 6, 15), 5)
expect(result[0]).to_equal(2020)
```

</details>

### Date Calculate - Comparison

#### equal

#### returns true for same dates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(equal((2025, 1, 15), (2025, 1, 15))).to_equal(true)
```

</details>

#### returns false for different years

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(equal((2025, 1, 15), (2024, 1, 15))).to_equal(false)
```

</details>

#### returns false for different months

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(equal((2025, 1, 15), (2025, 2, 15))).to_equal(false)
```

</details>

#### returns false for different days

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(equal((2025, 1, 15), (2025, 1, 16))).to_equal(false)
```

</details>

#### before

#### returns true when date1 is earlier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(before((2025, 1, 1), (2025, 1, 2))).to_equal(true)
```

</details>

#### returns false when date1 is later

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(before((2025, 1, 2), (2025, 1, 1))).to_equal(false)
```

</details>

#### returns false for same date

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(before((2025, 1, 1), (2025, 1, 1))).to_equal(false)
```

</details>

#### after

#### returns true when date1 is later

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(after((2025, 1, 2), (2025, 1, 1))).to_equal(true)
```

</details>

#### returns false when date1 is earlier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(after((2025, 1, 1), (2025, 1, 2))).to_equal(false)
```

</details>

#### returns false for same date

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(after((2025, 1, 1), (2025, 1, 1))).to_equal(false)
```

</details>

#### compare

#### returns -1 for before

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compare((2025, 1, 1), (2025, 1, 2))).to_equal(-1)
```

</details>

#### returns 1 for after

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compare((2025, 1, 2), (2025, 1, 1))).to_equal(1)
```

</details>

#### returns 0 for equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compare((2025, 1, 1), (2025, 1, 1))).to_equal(0)
```

</details>

#### before_or_equal

#### returns true for before

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(before_or_equal((2025, 1, 1), (2025, 1, 2))).to_equal(true)
```

</details>

#### returns true for equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(before_or_equal((2025, 1, 1), (2025, 1, 1))).to_equal(true)
```

</details>

#### returns false for after

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(before_or_equal((2025, 1, 2), (2025, 1, 1))).to_equal(false)
```

</details>

#### after_or_equal

#### returns true for after

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(after_or_equal((2025, 1, 2), (2025, 1, 1))).to_equal(true)
```

</details>

#### returns true for equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(after_or_equal((2025, 1, 1), (2025, 1, 1))).to_equal(true)
```

</details>

#### returns false for before

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(after_or_equal((2025, 1, 1), (2025, 1, 2))).to_equal(false)
```

</details>

### Date Calculate - Calendar Navigation

#### first_day_of_month

#### returns first day

- var result = first day of month
   - Expected: result[2] equals `1`
   - Expected: result[1] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = first_day_of_month((2025, 3, 15))
expect(result[2]).to_equal(1)
expect(result[1]).to_equal(3)
```

</details>

#### last_day_of_month

#### returns 31 for January

- var result = last day of month
   - Expected: result[2] equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = last_day_of_month((2025, 1, 15))
expect(result[2]).to_equal(31)
```

</details>

#### returns 28 for February non-leap

- var result = last day of month
   - Expected: result[2] equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = last_day_of_month((2025, 2, 10))
expect(result[2]).to_equal(28)
```

</details>

#### returns 29 for February leap

- var result = last day of month
   - Expected: result[2] equals `29`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = last_day_of_month((2024, 2, 10))
expect(result[2]).to_equal(29)
```

</details>

#### first_day_of_year

#### returns January 1

- var result = first day of year
   - Expected: result[1] equals `1`
   - Expected: result[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = first_day_of_year((2025, 6, 15))
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(1)
```

</details>

#### last_day_of_year

#### returns December 31

- var result = last day of year
   - Expected: result[1] equals `12`
   - Expected: result[2] equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = last_day_of_year((2025, 6, 15))
expect(result[1]).to_equal(12)
expect(result[2]).to_equal(31)
```

</details>

#### first_day_of_quarter

#### returns Jan 1 for Q1

- var result = first day of quarter
   - Expected: result[1] equals `1`
   - Expected: result[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = first_day_of_quarter((2025, 2, 15))
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(1)
```

</details>

#### returns Apr 1 for Q2

- var result = first day of quarter
   - Expected: result[1] equals `4`
   - Expected: result[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = first_day_of_quarter((2025, 5, 15))
expect(result[1]).to_equal(4)
expect(result[2]).to_equal(1)
```

</details>

#### returns Jul 1 for Q3

- var result = first day of quarter
   - Expected: result[1] equals `7`
   - Expected: result[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = first_day_of_quarter((2025, 8, 15))
expect(result[1]).to_equal(7)
expect(result[2]).to_equal(1)
```

</details>

#### returns Oct 1 for Q4

- var result = first day of quarter
   - Expected: result[1] equals `10`
   - Expected: result[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = first_day_of_quarter((2025, 11, 15))
expect(result[1]).to_equal(10)
expect(result[2]).to_equal(1)
```

</details>

#### last_day_of_quarter

#### returns Mar 31 for Q1

- var result = last day of quarter
   - Expected: result[1] equals `3`
   - Expected: result[2] equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = last_day_of_quarter((2025, 2, 15))
expect(result[1]).to_equal(3)
expect(result[2]).to_equal(31)
```

</details>

#### returns Jun 30 for Q2

- var result = last day of quarter
   - Expected: result[1] equals `6`
   - Expected: result[2] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = last_day_of_quarter((2025, 5, 15))
expect(result[1]).to_equal(6)
expect(result[2]).to_equal(30)
```

</details>

#### returns Sep 30 for Q3

- var result = last day of quarter
   - Expected: result[1] equals `9`
   - Expected: result[2] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = last_day_of_quarter((2025, 8, 15))
expect(result[1]).to_equal(9)
expect(result[2]).to_equal(30)
```

</details>

#### returns Dec 31 for Q4

- var result = last day of quarter
   - Expected: result[1] equals `12`
   - Expected: result[2] equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = last_day_of_quarter((2025, 11, 15))
expect(result[1]).to_equal(12)
expect(result[2]).to_equal(31)
```

</details>

### Date Calculate - Nth Day of Month

#### finds 1st Monday of January 2025

- var result = nth day of month
- check
   - Expected: result[2] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Jan 1, 2025 is Wednesday, so 1st Monday is Jan 6
var result = nth_day_of_month((2025, 1, 1), 1, 1)
check(result != nil)
expect(result[2]).to_equal(6)
```

</details>

#### finds 2nd Friday of January 2025

- var result = nth day of month
- check
   - Expected: result[2] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = nth_day_of_month((2025, 1, 1), 2, 5)
check(result != nil)
expect(result[2]).to_equal(10)
```

</details>

#### returns nil for 5th Monday when it does not exist

- var result = nth day of month
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Not every month has a 5th Monday
var result = nth_day_of_month((2025, 2, 1), 5, 1)
expect(result).to_equal(nil)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 65 |
| Active scenarios | 65 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
