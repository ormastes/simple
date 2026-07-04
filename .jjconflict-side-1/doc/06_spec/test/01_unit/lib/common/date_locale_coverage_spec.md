# Date Locale Coverage Test Suite

> Branch coverage tests for locale-aware date formatting and edge cases:

<!-- sdn-diagram:id=date_locale_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=date_locale_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

date_locale_coverage_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=date_locale_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 89 | 89 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Date Locale Coverage Test Suite

Branch coverage tests for locale-aware date formatting and edge cases:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DATE_LOCALE_COVERAGE |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/lib/common/date_locale_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Branch coverage tests for locale-aware date formatting and edge cases:
- src/lib/common/locale/dates.spl (locale month/day names, format_date, format_time, relative time)
- Edge cases and boundary conditions for date arithmetic

## Scenarios

### Locale Dates - Month Name

#### English locale

#### returns January for month 1

- var locale =
   - Expected: locale_month_name(1, locale) equals `January`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_month_name(1, locale)).to_equal("January")
```

</details>

#### returns December for month 12

- var locale =
   - Expected: locale_month_name(12, locale) equals `December`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_month_name(12, locale)).to_equal("December")
```

</details>

#### returns empty for invalid month

- var locale =
   - Expected: locale_month_name(0, locale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_month_name(0, locale)).to_equal("")
```

</details>

#### French locale

#### returns janvier for month 1

- var locale =
   - Expected: locale_month_name(1, locale) equals `janvier`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_month_name(1, locale)).to_equal("janvier")
```

</details>

#### returns décembre for month 12

- var locale =
   - Expected: locale_month_name(12, locale) equals `"décembre")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_month_name(12, locale)).to_equal("décembre")
```

</details>

#### returns empty for invalid month

- var locale =
   - Expected: locale_month_name(0, locale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_month_name(0, locale)).to_equal("")
```

</details>

#### Spanish locale

#### returns enero for month 1

- var locale =
   - Expected: locale_month_name(1, locale) equals `enero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_month_name(1, locale)).to_equal("enero")
```

</details>

#### returns diciembre for month 12

- var locale =
   - Expected: locale_month_name(12, locale) equals `diciembre`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_month_name(12, locale)).to_equal("diciembre")
```

</details>

#### returns empty for invalid month

- var locale =
   - Expected: locale_month_name(0, locale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_month_name(0, locale)).to_equal("")
```

</details>

#### German locale

#### returns Januar for month 1

- var locale =
   - Expected: locale_month_name(1, locale) equals `Januar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
expect(locale_month_name(1, locale)).to_equal("Januar")
```

</details>

#### returns Dezember for month 12

- var locale =
   - Expected: locale_month_name(12, locale) equals `Dezember`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
expect(locale_month_name(12, locale)).to_equal("Dezember")
```

</details>

#### returns empty for invalid month

- var locale =
   - Expected: locale_month_name(0, locale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
expect(locale_month_name(0, locale)).to_equal("")
```

</details>

### Locale Dates - Month Name Short

#### returns 3-char abbreviation for English

- var locale =
   - Expected: locale_month_name_short(1, locale) equals `Jan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_month_name_short(1, locale)).to_equal("Jan")
```

</details>

#### returns 3-char abbreviation for French

- var locale =
   - Expected: locale_month_name_short(1, locale) equals `jan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_month_name_short(1, locale)).to_equal("jan")
```

</details>

#### returns full name when shorter than 3 chars

- var locale =
- var result = locale month name short
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Empty string for invalid month has length < 3
var locale = ("en", "US", "", "")
var result = locale_month_name_short(0, locale)
expect(result).to_equal("")
```

</details>

### Locale Dates - Day Name

#### English locale

#### returns Monday for day 1

- var locale =
   - Expected: locale_day_name(1, locale) equals `Monday`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_day_name(1, locale)).to_equal("Monday")
```

</details>

#### returns Sunday for day 7

- var locale =
   - Expected: locale_day_name(7, locale) equals `Sunday`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_day_name(7, locale)).to_equal("Sunday")
```

</details>

#### returns empty for invalid day

- var locale =
   - Expected: locale_day_name(0, locale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_day_name(0, locale)).to_equal("")
```

</details>

#### French locale

#### returns lundi for day 1

- var locale =
   - Expected: locale_day_name(1, locale) equals `lundi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_day_name(1, locale)).to_equal("lundi")
```

</details>

#### returns dimanche for day 7

- var locale =
   - Expected: locale_day_name(7, locale) equals `dimanche`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_day_name(7, locale)).to_equal("dimanche")
```

</details>

#### returns empty for invalid day

- var locale =
   - Expected: locale_day_name(0, locale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_day_name(0, locale)).to_equal("")
```

</details>

#### Spanish locale

#### returns lunes for day 1

- var locale =
   - Expected: locale_day_name(1, locale) equals `lunes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_day_name(1, locale)).to_equal("lunes")
```

</details>

#### returns domingo for day 7

- var locale =
   - Expected: locale_day_name(7, locale) equals `domingo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_day_name(7, locale)).to_equal("domingo")
```

</details>

#### returns empty for invalid day

- var locale =
   - Expected: locale_day_name(0, locale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_day_name(0, locale)).to_equal("")
```

</details>

#### German locale

#### returns Montag for day 1

- var locale =
   - Expected: locale_day_name(1, locale) equals `Montag`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
expect(locale_day_name(1, locale)).to_equal("Montag")
```

</details>

#### returns Sonntag for day 7

- var locale =
   - Expected: locale_day_name(7, locale) equals `Sonntag`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
expect(locale_day_name(7, locale)).to_equal("Sonntag")
```

</details>

#### returns empty for invalid day

- var locale =
   - Expected: locale_day_name(0, locale) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("de", "DE", "", "")
expect(locale_day_name(0, locale)).to_equal("")
```

</details>

### Locale Dates - Day Name Short

#### returns 3-char abbreviation for English Monday

- var locale =
   - Expected: locale_day_name_short(1, locale) equals `Mon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_day_name_short(1, locale)).to_equal("Mon")
```

</details>

#### returns 3-char abbreviation for French lundi

- var locale =
   - Expected: locale_day_name_short(1, locale) equals `lun`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_day_name_short(1, locale)).to_equal("lun")
```

</details>

#### returns full name when shorter than 3 chars

- var locale =
- var result = locale day name short
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_day_name_short(0, locale)
expect(result).to_equal("")
```

</details>

### Locale Dates - format_date

#### formats yyyy-MM-dd pattern

- var locale =
- var result = locale format date
   - Expected: result equals `2026-02-11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_date(2026, 2, 11, "yyyy-MM-dd", locale)
expect(result).to_equal("2026-02-11")
```

</details>

#### pads month with leading zero

- var locale =
- var result = locale format date


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_date(2026, 2, 11, "yyyy-MM-dd", locale)
expect(result).to_contain("-02-")
```

</details>

#### does not pad month 10

- var locale =
- var result = locale format date


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_date(2026, 10, 5, "yyyy-MM-dd", locale)
expect(result).to_contain("-10-")
```

</details>

#### pads day with leading zero

- var locale =
- var result = locale format date


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_date(2026, 2, 5, "yyyy-MM-dd", locale)
expect(result).to_end_with("-05")
```

</details>

#### does not pad day 15

- var locale =
- var result = locale format date


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_date(2026, 2, 15, "yyyy-MM-dd", locale)
expect(result).to_end_with("-15")
```

</details>

#### formats with full month name pattern

- var locale =
- var result = locale format date


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_date(2026, 2, 11, "MMMM dd, yyyy", locale)
expect(result).to_contain("February")
```

</details>

#### formats with short month name pattern

- var locale =
- var result = locale format date


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_date(2026, 2, 11, "MMM dd, yyyy", locale)
expect(result).to_contain("Feb")
```

</details>

#### formats with French locale full month

- var locale =
- var result = locale format date


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
var result = locale_format_date(2026, 2, 11, "MMMM dd, yyyy", locale)
expect(result).to_contain("vri")
```

</details>

### Locale Dates - format_time

#### formats HH:mm:ss pattern

- var locale =
- var result = locale format time
   - Expected: result equals `14:30:00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(14, 30, 0, "HH:mm:ss", locale)
expect(result).to_equal("14:30:00")
```

</details>

#### pads hour with leading zero

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(9, 30, 0, "HH:mm:ss", locale)
expect(result).to_start_with("09")
```

</details>

#### does not pad hour 14

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(14, 30, 0, "HH:mm:ss", locale)
expect(result).to_start_with("14")
```

</details>

#### formats 12-hour with PM

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(14, 30, 0, "hh:mm a", locale)
expect(result).to_contain("PM")
```

</details>

#### formats 12-hour with AM

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(9, 30, 0, "hh:mm a", locale)
expect(result).to_contain("AM")
```

</details>

#### converts hour 0 to 12 in 12-hour format

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(0, 0, 0, "hh:mm a", locale)
expect(result).to_start_with("12")
expect(result).to_contain("AM")
```

</details>

#### converts hour 12 to 12 in 12-hour format

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(12, 0, 0, "hh:mm a", locale)
expect(result).to_start_with("12")
expect(result).to_contain("PM")
```

</details>

#### pads 12-hour when less than 10

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(1, 0, 0, "hh:mm a", locale)
expect(result).to_start_with("01")
```

</details>

#### does not pad 12-hour when 10 or more

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(22, 0, 0, "hh:mm a", locale)
expect(result).to_start_with("10")
```

</details>

#### pads minute with leading zero

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(14, 5, 0, "HH:mm:ss", locale)
expect(result).to_contain(":05:")
```

</details>

#### does not pad minute 30

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(14, 30, 0, "HH:mm:ss", locale)
expect(result).to_contain(":30:")
```

</details>

#### pads second with leading zero

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(14, 30, 5, "HH:mm:ss", locale)
expect(result).to_end_with(":05")
```

</details>

#### does not pad second 45

- var locale =
- var result = locale format time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
var result = locale_format_time(14, 30, 45, "HH:mm:ss", locale)
expect(result).to_end_with(":45")
```

</details>

### Locale Dates - Relative Time

#### English locale

#### formats seconds ago

- var locale =
   - Expected: locale_relative_time_seconds(-30, locale) equals `a few seconds ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(-30, locale)).to_equal("a few seconds ago")
```

</details>

#### formats seconds in future

- var locale =
   - Expected: locale_relative_time_seconds(30, locale) equals `in a few seconds`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(30, locale)).to_equal("in a few seconds")
```

</details>

#### formats minutes ago

- var locale =
   - Expected: locale_relative_time_seconds(-300, locale) equals `5 minutes ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(-300, locale)).to_equal("5 minutes ago")
```

</details>

#### formats minutes in future

- var locale =
   - Expected: locale_relative_time_seconds(300, locale) equals `in 5 minutes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(300, locale)).to_equal("in 5 minutes")
```

</details>

#### formats hours ago

- var locale =
   - Expected: locale_relative_time_seconds(-7200, locale) equals `2 hours ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(-7200, locale)).to_equal("2 hours ago")
```

</details>

#### formats hours in future

- var locale =
   - Expected: locale_relative_time_seconds(7200, locale) equals `in 2 hours`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(7200, locale)).to_equal("in 2 hours")
```

</details>

#### formats days ago

- var locale =
   - Expected: locale_relative_time_seconds(-172800, locale) equals `2 days ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(-172800, locale)).to_equal("2 days ago")
```

</details>

#### formats days in future

- var locale =
   - Expected: locale_relative_time_seconds(172800, locale) equals `in 2 days`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_relative_time_seconds(172800, locale)).to_equal("in 2 days")
```

</details>

#### French locale

#### formats seconds ago in French

- var locale =
   - Expected: locale_relative_time_seconds(-30, locale) equals `il y a quelques secondes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_relative_time_seconds(-30, locale)).to_equal("il y a quelques secondes")
```

</details>

#### formats seconds in future in French

- var locale =
   - Expected: locale_relative_time_seconds(30, locale) equals `dans quelques secondes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_relative_time_seconds(30, locale)).to_equal("dans quelques secondes")
```

</details>

#### formats minutes ago in French

- var locale =
   - Expected: locale_relative_time_seconds(-300, locale) equals `il y a 5 minutes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_relative_time_seconds(-300, locale)).to_equal("il y a 5 minutes")
```

</details>

#### formats minutes in future in French

- var locale =
   - Expected: locale_relative_time_seconds(300, locale) equals `dans 5 minutes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_relative_time_seconds(300, locale)).to_equal("dans 5 minutes")
```

</details>

#### formats hours ago in French

- var locale =
   - Expected: locale_relative_time_seconds(-7200, locale) equals `il y a 2 heures`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_relative_time_seconds(-7200, locale)).to_equal("il y a 2 heures")
```

</details>

#### formats hours in future in French

- var locale =
   - Expected: locale_relative_time_seconds(7200, locale) equals `dans 2 heures`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_relative_time_seconds(7200, locale)).to_equal("dans 2 heures")
```

</details>

#### formats days ago in French

- var locale =
   - Expected: locale_relative_time_seconds(-172800, locale) equals `il y a 2 jours`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_relative_time_seconds(-172800, locale)).to_equal("il y a 2 jours")
```

</details>

#### formats days in future in French

- var locale =
   - Expected: locale_relative_time_seconds(172800, locale) equals `dans 2 jours`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("fr", "FR", "", "")
expect(locale_relative_time_seconds(172800, locale)).to_equal("dans 2 jours")
```

</details>

#### Spanish locale

#### formats seconds ago in Spanish

- var locale =
   - Expected: locale_relative_time_seconds(-30, locale) equals `hace unos segundos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_relative_time_seconds(-30, locale)).to_equal("hace unos segundos")
```

</details>

#### formats seconds in future in Spanish

- var locale =
   - Expected: locale_relative_time_seconds(30, locale) equals `en unos segundos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_relative_time_seconds(30, locale)).to_equal("en unos segundos")
```

</details>

#### formats minutes ago in Spanish

- var locale =
   - Expected: locale_relative_time_seconds(-300, locale) equals `hace 5 minutos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_relative_time_seconds(-300, locale)).to_equal("hace 5 minutos")
```

</details>

#### formats minutes in future in Spanish

- var locale =
   - Expected: locale_relative_time_seconds(300, locale) equals `en 5 minutos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
expect(locale_relative_time_seconds(300, locale)).to_equal("en 5 minutos")
```

</details>

#### formats hours ago in Spanish

- var locale =
- var result = locale relative time seconds
   - Expected: result equals `hace 2 horas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
var result = locale_relative_time_seconds(-7200, locale)
expect(result).to_equal("hace 2 horas")
```

</details>

#### formats hours in future in Spanish

- var locale =
- var result = locale relative time seconds
   - Expected: result equals `en 2 horas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
var result = locale_relative_time_seconds(7200, locale)
expect(result).to_equal("en 2 horas")
```

</details>

#### formats days ago in Spanish

- var locale =
- var result = locale relative time seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
var result = locale_relative_time_seconds(-172800, locale)
expect(result).to_contain("hace 2")
```

</details>

#### formats days in future in Spanish

- var locale =
- var result = locale relative time seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("es", "ES", "", "")
var result = locale_relative_time_seconds(172800, locale)
expect(result).to_contain("en 2")
```

</details>

#### time_ago and time_until wrappers

#### time_ago delegates to relative_time_seconds

- var locale =
   - Expected: locale_time_ago(-3600, locale) equals `1 hours ago`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_time_ago(-3600, locale)).to_equal("1 hours ago")
```

</details>

#### time_until delegates to relative_time_seconds

- var locale =
   - Expected: locale_time_until(3600, locale) equals `in 1 hours`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var locale = ("en", "US", "", "")
expect(locale_time_until(3600, locale)).to_equal("in 1 hours")
```

</details>

### Edge Cases - Leap Year Boundaries

#### Feb 28 is valid on non-leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 2, 28)).to_equal(true)
```

</details>

#### Feb 29 is invalid on non-leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2025, 2, 29)).to_equal(false)
```

</details>

#### Feb 29 is valid on leap year

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2024, 2, 29)).to_equal(true)
```

</details>

#### Feb 29 is valid on year 2000 (div by 400)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(2000, 2, 29)).to_equal(true)
```

</details>

#### Feb 29 is invalid on year 1900 (div by 100 not 400)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_date(1900, 2, 29)).to_equal(false)
```

</details>

### Edge Cases - Day of Year Boundaries

#### Dec 31 non-leap returns 365

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2025, 12, 31))).to_equal(365)
```

</details>

#### Dec 31 leap returns 366

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2024, 12, 31))).to_equal(366)
```

</details>

#### Mar 1 non-leap returns 60

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2025, 3, 1))).to_equal(60)
```

</details>

#### Mar 1 leap returns 61

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(day_of_year((2024, 3, 1))).to_equal(61)
```

</details>

### Edge Cases - Month Arithmetic Overflow

#### adding 12 months equals next year

- var result = add months
   - Expected: result[0] equals `2026`
   - Expected: result[1] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_months((2025, 6, 15), 12)
expect(result[0]).to_equal(2026)
expect(result[1]).to_equal(6)
```

</details>

#### adding 24 months equals two years later

- var result = add months
   - Expected: result[0] equals `2027`
   - Expected: result[1] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_months((2025, 6, 15), 24)
expect(result[0]).to_equal(2027)
expect(result[1]).to_equal(6)
```

</details>

#### subtracting 12 months equals previous year

- var result = add months
   - Expected: result[0] equals `2024`
   - Expected: result[1] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = add_months((2025, 6, 15), -12)
expect(result[0]).to_equal(2024)
expect(result[1]).to_equal(6)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 89 |
| Active scenarios | 89 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
