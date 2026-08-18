# formula_date_spec

> Calc date functions spec — DATE/YEAR/MONTH/DAY/DAYS/WEEKDAY/EDATE (113 total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_date_spec

Calc date functions spec — DATE/YEAR/MONTH/DAY/DAYS/WEEKDAY/EDATE (113 total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_date_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc date functions spec — DATE/YEAR/MONTH/DAY/DAYS/WEEKDAY/EDATE (113 total).

Pure integer civil<->serial conversion (Hinnant's algorithms), Excel 1900
serial system. Anchors: 1970-01-01 = 25569, 2000-01-01 = 36526; WEEKDAY uses
Excel's default Sunday=1; EDATE clamps month-end (Jan 31 + 1mo = Feb 28).

## Scenarios

### Calc dates: serial conversion

#### matches known Excel serial anchors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DATE(1970, 1, 1)")).to_equal("25569")
expect(_eval("=DATE(2000, 1, 1)")).to_equal("36526")
```

</details>

#### round-trips year/month/day through the serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=YEAR(DATE(2026, 7, 3))")).to_equal("2026")
expect(_eval("=MONTH(DATE(2026, 7, 3))")).to_equal("7")
expect(_eval("=DAY(DATE(2026, 7, 3))")).to_equal("3")
```

</details>

### Calc dates: arithmetic

#### DAYS subtracts serials and WEEKDAY uses Sunday=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DAYS(DATE(2026, 7, 3), DATE(2026, 6, 3))")).to_equal("30")
expect(_eval("=WEEKDAY(DATE(2026, 7, 3))")).to_equal("6")
expect(_eval("=WEEKDAY(DATE(2026, 7, 5))")).to_equal("1")
```

</details>

#### EDATE shifts months and clamps month-end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DAY(EDATE(DATE(2026, 1, 31), 1))")).to_equal("28")
expect(_eval("=MONTH(EDATE(DATE(2026, 11, 15), 3))")).to_equal("2")
expect(_eval("=YEAR(EDATE(DATE(2026, 11, 15), 3))")).to_equal("2027")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
