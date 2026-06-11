# Date Module Coverage Test Suite

> Comprehensive branch coverage tests for:

<!-- sdn-diagram:id=date_edge_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=date_edge_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

date_edge_coverage_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=date_edge_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

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
| Source | `test/01_unit/lib/common/date_edge_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Comprehensive branch coverage tests for:
- src/lib/common/date/types.spl (constants, validation, properties)
- src/lib/common/date/format.spl (date formatting)
- src/lib/common/date/calculate.spl (arithmetic, comparison, calendar)
- src/lib/common/locale/dates.spl (locale-aware formatting, relative time)

## Scenarios

### Edge Cases - Constants Verification

#### MONDAY equals 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MONDAY).to_equal(1)
```

</details>

#### SUNDAY equals 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SUNDAY).to_equal(7)
```

</details>

#### THURSDAY equals 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(THURSDAY).to_equal(4)
```

</details>

#### JANUARY equals 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JANUARY).to_equal(1)
```

</details>

#### DECEMBER equals 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DECEMBER).to_equal(12)
```

</details>

#### FEBRUARY equals 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(FEBRUARY).to_equal(2)
```

</details>

#### TUESDAY equals 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TUESDAY).to_equal(2)
```

</details>

#### WEDNESDAY equals 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WEDNESDAY).to_equal(3)
```

</details>

#### FRIDAY equals 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(FRIDAY).to_equal(5)
```

</details>

#### SATURDAY equals 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SATURDAY).to_equal(6)
```

</details>

#### MARCH equals 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MARCH).to_equal(3)
```

</details>

#### APRIL equals 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(APRIL).to_equal(4)
```

</details>

#### MAY equals 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MAY).to_equal(5)
```

</details>

#### JUNE equals 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JUNE).to_equal(6)
```

</details>

#### JULY equals 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JULY).to_equal(7)
```

</details>

#### AUGUST equals 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(AUGUST).to_equal(8)
```

</details>

#### SEPTEMBER equals 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SEPTEMBER).to_equal(9)
```

</details>

#### OCTOBER equals 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(OCTOBER).to_equal(10)
```

</details>

#### NOVEMBER equals 11

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NOVEMBER).to_equal(11)
```

</details>

### Locale Month Name - All French months

#### returns all French month names

1. var locale =
   - Expected: locale_month_name(2, locale) equals `"février")`
   - Expected: locale_month_name(3, locale) equals `mars`
   - Expected: locale_month_name(4, locale) equals `avril`
   - Expected: locale_month_name(5, locale) equals `mai`
   - Expected: locale_month_name(6, locale) equals `juin`
   - Expected: locale_month_name(7, locale) equals `juillet`
   - Expected: locale_month_name(8, locale) equals `"août")`
   - Expected: locale_month_name(9, locale) equals `septembre`
   - Expected: locale_month_name(10, locale) equals `octobre`
   - Expected: locale_month_name(11, locale) equals `novembre`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_month_name(2, locale)).to_equal("février")
expect(locale_month_name(3, locale)).to_equal("mars")
expect(locale_month_name(4, locale)).to_equal("avril")
expect(locale_month_name(5, locale)).to_equal("mai")
expect(locale_month_name(6, locale)).to_equal("juin")
expect(locale_month_name(7, locale)).to_equal("juillet")
expect(locale_month_name(8, locale)).to_equal("août")
expect(locale_month_name(9, locale)).to_equal("septembre")
expect(locale_month_name(10, locale)).to_equal("octobre")
expect(locale_month_name(11, locale)).to_equal("novembre")
```

</details>

### Locale Month Name - All Spanish months

#### returns all Spanish month names

1. var locale =
   - Expected: locale_month_name(2, locale) equals `febrero`
   - Expected: locale_month_name(3, locale) equals `marzo`
   - Expected: locale_month_name(4, locale) equals `abril`
   - Expected: locale_month_name(5, locale) equals `mayo`
   - Expected: locale_month_name(6, locale) equals `junio`
   - Expected: locale_month_name(7, locale) equals `julio`
   - Expected: locale_month_name(8, locale) equals `agosto`
   - Expected: locale_month_name(9, locale) equals `septiembre`
   - Expected: locale_month_name(10, locale) equals `octubre`
   - Expected: locale_month_name(11, locale) equals `noviembre`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_month_name(2, locale)).to_equal("febrero")
expect(locale_month_name(3, locale)).to_equal("marzo")
expect(locale_month_name(4, locale)).to_equal("abril")
expect(locale_month_name(5, locale)).to_equal("mayo")
expect(locale_month_name(6, locale)).to_equal("junio")
expect(locale_month_name(7, locale)).to_equal("julio")
expect(locale_month_name(8, locale)).to_equal("agosto")
expect(locale_month_name(9, locale)).to_equal("septiembre")
expect(locale_month_name(10, locale)).to_equal("octubre")
expect(locale_month_name(11, locale)).to_equal("noviembre")
```

</details>

### Locale Month Name - All German months

#### returns all German month names

1. var locale =
   - Expected: locale_month_name(2, locale) equals `Februar`
   - Expected: locale_month_name(3, locale) equals `"März")`
   - Expected: locale_month_name(4, locale) equals `April`
   - Expected: locale_month_name(5, locale) equals `Mai`
   - Expected: locale_month_name(6, locale) equals `Juni`
   - Expected: locale_month_name(7, locale) equals `Juli`
   - Expected: locale_month_name(8, locale) equals `August`
   - Expected: locale_month_name(9, locale) equals `September`
   - Expected: locale_month_name(10, locale) equals `Oktober`
   - Expected: locale_month_name(11, locale) equals `November`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
expect(locale_month_name(2, locale)).to_equal("Februar")
expect(locale_month_name(3, locale)).to_equal("März")
expect(locale_month_name(4, locale)).to_equal("April")
expect(locale_month_name(5, locale)).to_equal("Mai")
expect(locale_month_name(6, locale)).to_equal("Juni")
expect(locale_month_name(7, locale)).to_equal("Juli")
expect(locale_month_name(8, locale)).to_equal("August")
expect(locale_month_name(9, locale)).to_equal("September")
expect(locale_month_name(10, locale)).to_equal("Oktober")
expect(locale_month_name(11, locale)).to_equal("November")
```

</details>

### Locale Month Name - All English months

#### returns all English month names

1. var locale =
   - Expected: locale_month_name(2, locale) equals `February`
   - Expected: locale_month_name(3, locale) equals `March`
   - Expected: locale_month_name(4, locale) equals `April`
   - Expected: locale_month_name(5, locale) equals `May`
   - Expected: locale_month_name(6, locale) equals `June`
   - Expected: locale_month_name(7, locale) equals `July`
   - Expected: locale_month_name(8, locale) equals `August`
   - Expected: locale_month_name(9, locale) equals `September`
   - Expected: locale_month_name(10, locale) equals `October`
   - Expected: locale_month_name(11, locale) equals `November`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_month_name(2, locale)).to_equal("February")
expect(locale_month_name(3, locale)).to_equal("March")
expect(locale_month_name(4, locale)).to_equal("April")
expect(locale_month_name(5, locale)).to_equal("May")
expect(locale_month_name(6, locale)).to_equal("June")
expect(locale_month_name(7, locale)).to_equal("July")
expect(locale_month_name(8, locale)).to_equal("August")
expect(locale_month_name(9, locale)).to_equal("September")
expect(locale_month_name(10, locale)).to_equal("October")
expect(locale_month_name(11, locale)).to_equal("November")
```

</details>

### Locale Day Name - All French days

#### returns all French day names

1. var locale =
   - Expected: locale_day_name(2, locale) equals `mardi`
   - Expected: locale_day_name(3, locale) equals `mercredi`
   - Expected: locale_day_name(4, locale) equals `jeudi`
   - Expected: locale_day_name(5, locale) equals `vendredi`
   - Expected: locale_day_name(6, locale) equals `samedi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_day_name(2, locale)).to_equal("mardi")
expect(locale_day_name(3, locale)).to_equal("mercredi")
expect(locale_day_name(4, locale)).to_equal("jeudi")
expect(locale_day_name(5, locale)).to_equal("vendredi")
expect(locale_day_name(6, locale)).to_equal("samedi")
```

</details>

### Locale Day Name - All Spanish days

#### returns all Spanish day names

1. var locale =
   - Expected: locale_day_name(2, locale) equals `martes`
   - Expected: locale_day_name(3, locale) equals `"miércoles")`
   - Expected: locale_day_name(4, locale) equals `jueves`
   - Expected: locale_day_name(5, locale) equals `viernes`
   - Expected: locale_day_name(6, locale) equals `"sábado")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_day_name(2, locale)).to_equal("martes")
expect(locale_day_name(3, locale)).to_equal("miércoles")
expect(locale_day_name(4, locale)).to_equal("jueves")
expect(locale_day_name(5, locale)).to_equal("viernes")
expect(locale_day_name(6, locale)).to_equal("sábado")
```

</details>

### Locale Day Name - All German days

#### returns all German day names

1. var locale =
   - Expected: locale_day_name(2, locale) equals `Dienstag`
   - Expected: locale_day_name(3, locale) equals `Mittwoch`
   - Expected: locale_day_name(4, locale) equals `Donnerstag`
   - Expected: locale_day_name(5, locale) equals `Freitag`
   - Expected: locale_day_name(6, locale) equals `Samstag`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
expect(locale_day_name(2, locale)).to_equal("Dienstag")
expect(locale_day_name(3, locale)).to_equal("Mittwoch")
expect(locale_day_name(4, locale)).to_equal("Donnerstag")
expect(locale_day_name(5, locale)).to_equal("Freitag")
expect(locale_day_name(6, locale)).to_equal("Samstag")
```

</details>

### Locale Day Name - All English days

#### returns all English day names

1. var locale =
   - Expected: locale_day_name(2, locale) equals `Tuesday`
   - Expected: locale_day_name(3, locale) equals `Wednesday`
   - Expected: locale_day_name(4, locale) equals `Thursday`
   - Expected: locale_day_name(5, locale) equals `Friday`
   - Expected: locale_day_name(6, locale) equals `Saturday`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_day_name(2, locale)).to_equal("Tuesday")
expect(locale_day_name(3, locale)).to_equal("Wednesday")
expect(locale_day_name(4, locale)).to_equal("Thursday")
expect(locale_day_name(5, locale)).to_equal("Friday")
expect(locale_day_name(6, locale)).to_equal("Saturday")
```

</details>

### Format - text_from_i64 all digits

#### converts numbers with all digits 0-9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(1023456789)).to_equal("1023456789")
```

</details>

#### converts number with digit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(10)).to_equal("10")
```

</details>

#### converts number with digit 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(6)).to_equal("6")
```

</details>

#### converts number with digit 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(7)).to_equal("7")
```

</details>

#### converts number with digit 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(8)).to_equal("8")
```

</details>

#### converts number with digit 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_from_i64(9)).to_equal("9")
```

</details>

### Locale Format Time - Additional branches

#### formats hour 0 (midnight) 24-hour

1. var locale =
2. var result = locale format time
   - Expected: result equals `00:00:00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(0, 0, 0, "HH:mm:ss", locale)
expect(result).to_equal("00:00:00")
```

</details>

#### formats 12-hour for hour 13 (PM)

1. var locale =
2. var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(13, 0, 0, "hh:mm a", locale)
expect(result).to_start_with("01")
expect(result).to_contain("PM")
```

</details>

### Locale Format Date - Additional branches

#### formats with German locale full month

1. var locale =
2. var result = locale format date


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
var result = locale_format_date(2026, 3, 15, "MMMM dd, yyyy", locale)
expect(result).to_contain("März")
```

</details>

#### formats with Spanish locale full month

1. var locale =
2. var result = locale format date


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
var result = locale_format_date(2026, 1, 15, "MMMM dd, yyyy", locale)
expect(result).to_contain("enero")
```

</details>

### Locale Relative Time - German locale

#### formats seconds ago in German

1. var locale =
2. var result = locale relative time seconds
   - Expected: result equals `a few seconds ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
var result = locale_relative_time_seconds(-30, locale)
expect(result).to_equal("a few seconds ago")
```

</details>

#### formats seconds in future in German

1. var locale =
2. var result = locale relative time seconds
   - Expected: result equals `in a few seconds`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
var result = locale_relative_time_seconds(30, locale)
expect(result).to_equal("in a few seconds")
```

</details>

#### formats minutes ago in German

1. var locale =
2. var result = locale relative time seconds
   - Expected: result equals `5 minutes ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
var result = locale_relative_time_seconds(-300, locale)
expect(result).to_equal("5 minutes ago")
```

</details>

#### formats minutes in future in German

1. var locale =
2. var result = locale relative time seconds
   - Expected: result equals `in 5 minutes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
var result = locale_relative_time_seconds(300, locale)
expect(result).to_equal("in 5 minutes")
```

</details>

#### formats hours ago in German

1. var locale =
2. var result = locale relative time seconds
   - Expected: result equals `2 hours ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
var result = locale_relative_time_seconds(-7200, locale)
expect(result).to_equal("2 hours ago")
```

</details>

#### formats hours in future in German

1. var locale =
2. var result = locale relative time seconds
   - Expected: result equals `in 2 hours`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
var result = locale_relative_time_seconds(7200, locale)
expect(result).to_equal("in 2 hours")
```

</details>

#### formats days ago in German

1. var locale =
2. var result = locale relative time seconds
   - Expected: result equals `2 days ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
var result = locale_relative_time_seconds(-172800, locale)
expect(result).to_equal("2 days ago")
```

</details>

#### formats days in future in German

1. var locale =
2. var result = locale relative time seconds
   - Expected: result equals `in 2 days`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
var result = locale_relative_time_seconds(172800, locale)
expect(result).to_equal("in 2 days")
```

</details>

### Locale Relative Time - Boundary

#### zero seconds

1. var locale =
2. var result = locale relative time seconds
   - Expected: result equals `a few seconds ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_relative_time_seconds(0, locale)
expect(result).to_equal("a few seconds ago")
```

</details>

#### exactly 60 seconds

1. var locale =
   - Expected: locale_relative_time_seconds(-60, locale) equals `1 minutes ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(-60, locale)).to_equal("1 minutes ago")
```

</details>

#### exactly 3600 seconds

1. var locale =
   - Expected: locale_relative_time_seconds(-3600, locale) equals `1 hours ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(-3600, locale)).to_equal("1 hours ago")
```

</details>

#### exactly 86400 seconds

1. var locale =
   - Expected: locale_relative_time_seconds(-86400, locale) equals `1 days ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(-86400, locale)).to_equal("1 days ago")
```

</details>

### Locale Short Names - Additional

#### short month name for German

1. var locale =
   - Expected: locale_month_name_short(1, locale) equals `Jan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
expect(locale_month_name_short(1, locale)).to_equal("Jan")
```

</details>

#### short month name for Spanish

1. var locale =
   - Expected: locale_month_name_short(1, locale) equals `ene`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_month_name_short(1, locale)).to_equal("ene")
```

</details>

#### short day name for German

1. var locale =
   - Expected: locale_day_name_short(1, locale) equals `Mon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
expect(locale_day_name_short(1, locale)).to_equal("Mon")
```

</details>

#### short day name for Spanish

1. var locale =
   - Expected: locale_day_name_short(1, locale) equals `lun`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_day_name_short(1, locale)).to_equal("lun")
```

</details>

#### short day name for invalid day

1. var locale =
   - Expected: locale_day_name_short(8, locale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_day_name_short(8, locale)).to_equal("")
```

</details>

#### short month name for invalid month

1. var locale =
   - Expected: locale_month_name_short(13, locale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_month_name_short(13, locale)).to_equal("")
```

</details>

### Calculate - age_in_years edge cases

#### same month day after birthday

1. var age = age in years
   - Expected: age equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var age = age_in_years((1990, 6, 15), (2025, 6, 16))
expect(age).to_equal(35)
```

</details>

#### birthday month later in year

1. var age = age in years
   - Expected: age equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var age = age_in_years((1990, 12, 25), (2025, 3, 15))
expect(age).to_equal(34)
```

</details>

### Calculate - difference_in_months edge cases

#### day1 greater than or equal to day2

1. var months = difference in months
   - Expected: months equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var months = difference_in_months((2025, 6, 20), (2025, 1, 15))
expect(months).to_equal(5)
```

</details>

#### negative month difference

1. var months = difference in months
   - Expected: months equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var months = difference_in_months((2025, 1, 15), (2025, 6, 15))
expect(months).to_equal(-5)
```

</details>

### Add Months - More overflow cases

#### adds months where total_months exactly 12

1. var result = add months
   - Expected: result[0] equals `2025`
   - Expected: result[1] equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_months((2025, 10, 15), 2)
expect(result[0]).to_equal(2025)
expect(result[1]).to_equal(12)
```

</details>

#### subtracts months where total is 0

1. var result = add months
   - Expected: result[0] equals `2024`
   - Expected: result[1] equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_months((2025, 3, 15), -3)
expect(result[0]).to_equal(2024)
expect(result[1]).to_equal(12)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 61 |
| Active scenarios | 61 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
