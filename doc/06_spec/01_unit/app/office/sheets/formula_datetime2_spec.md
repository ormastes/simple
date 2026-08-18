# formula_datetime2_spec

> Calc date/time + math fill-ins spec (DATETIME2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_datetime2_spec

Calc date/time + math fill-ins spec (DATETIME2).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_datetime2_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc date/time + math fill-ins spec (DATETIME2).

Every value pinned to an Excel documentation example or a hand recomputation
shown here:
  * TIME(6,0,0) = 21600/86400 = 0.25 ; TIME(12,30,0) = 45000/86400 = 0.520833...
  * TIMEVALUE("2:24 AM") = 8640/86400 = 0.1 (Excel docs example).
    Supported subset: "H:MM" / "H:MM:SS" 24-hour, optional space + AM/PM.
  * HOUR(0.75) = 18 ; MINUTE(TIME(12,30,0)) = 45000 s -> 750 min -> 30 ;
    SECOND(TIME(4,48,18)) = 17298 s -> 18.
  * ISOWEEKNUM(DATE(2012,3,9)) = 10 (Excel docs; Fri, Thursday-rule week 10).
    2016-01-01 (Fri) and 2005-01-01 (Sat) both land in ISO week 53 of the
    prior year.
  * DAYS360(2011-01-30, 2011-02-01) = 1 (Excel docs). US NASD Feb rule:
    DAYS360(2011-02-28, 2011-03-31) = 30 US / 32 European.
  * YEARFRAC(2012-01-01, 2012-07-30): basis0 209/360 = 0.580555...,
    basis1 211/366 = 0.576502..., basis3 211/365 = 0.578082... .
    CORRECTION: the task brief said basis3 = 0.575342 (= 210/365); actual
    day span Jan 1 -> Jul 30 2012 is 211 days, so 0.578082 (matches the MS
    docs value 0.57808219). Brief value rejected per ground-truth rule.
  * COMBINA(4,3) = COMBIN(6,3) = 20 ; PERMUTATIONA(3,2) = 3^2 = 9.
  * NETWORKDAYS.INTL(2026-07-01, 2026-07-10, 1) = 8 (Jul 1 2026 is a Wed;
    workdays 1,2,3,6,7,8,9,10). Weekend codes: numeric 1-7 / 11-17 only;
    the "0000011" string mask form is deferred (numeric arg path).
  * RAND / RANDBETWEEN ride the runtime RNG (rt_random_randint, inclusive
    bounds — probed); RANDBETWEEN(5,5) = 5 is the deterministic anchor.

## Scenarios

### Calc TIME

#### TIME(6,0,0) is 0.25

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TIME(6,0,0)")).to_equal("0.25")
```

</details>

#### TIME(12,30,0) is 0.520833...

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=TIME(12,30,0)", 0.5208333333, 0.0000001)).to_be(true)
```

</details>

#### wraps past midnight (TIME(27,0,0) = TIME(3,0,0))

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TIME(27,0,0)=TIME(3,0,0)")).to_equal("TRUE")
```

</details>

#### rolls over oversized minutes (TIME(0,90,0) = TIME(1,30,0))

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TIME(0,90,0)=TIME(1,30,0)")).to_equal("TRUE")
```

</details>

#### errors on negative components

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TIME(-1,0,0)")).to_contain("#ERR")
```

</details>

#### errors below 3 arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TIME(6,0)")).to_contain("#ERR")
```

</details>

### Calc TIMEVALUE

#### parses the Excel docs example 2:24 AM as 0.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=TIMEVALUE(\"2:24 AM\")", 0.1, 0.0000001)).to_be(true)
```

</details>

#### parses 6:00 AM as 0.25

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TIMEVALUE(\"6:00 AM\")")).to_equal("0.25")
```

</details>

#### parses 24-hour H:MM (14:30 = 0.604166...)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=TIMEVALUE(\"14:30\")", 0.6041666667, 0.0000001)).to_be(true)
```

</details>

#### parses H:MM:SS with PM (2:24:36 PM = 51876/86400)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=TIMEVALUE(\"2:24:36 PM\")", 0.6004166667, 0.0000001)).to_be(true)
```

</details>

#### 12 AM is midnight and 12:30 PM is 0.520833...

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TIMEVALUE(\"12:00 AM\")")).to_equal("0")
expect(_approx("=TIMEVALUE(\"12:30 PM\")", 0.5208333333, 0.0000001)).to_be(true)
```

</details>

#### rejects unparseable text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TIMEVALUE(\"banana\")")).to_contain("#ERR")
```

</details>

#### rejects out-of-range fields (25:00 and 7:75)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TIMEVALUE(\"25:00\")")).to_contain("#ERR")
expect(_eval("=TIMEVALUE(\"7:75\")")).to_contain("#ERR")
```

</details>

### Calc HOUR / MINUTE / SECOND

#### HOUR(0.75) is 18

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=HOUR(0.75)")).to_equal("18")
```

</details>

#### HOUR(TIME(6,0,0)) is 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=HOUR(TIME(6,0,0))")).to_equal("6")
```

</details>

#### MINUTE(TIME(12,30,0)) is 30 (exact serial, not a truncated literal)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=MINUTE(TIME(12,30,0))")).to_equal("30")
```

</details>

#### SECOND(TIME(4,48,18)) is 18

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SECOND(TIME(4,48,18))")).to_equal("18")
```

</details>

#### ignores the whole-day part of a serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=HOUR(DATE(2026,7,1)+0.25)")).to_equal("6")
```

</details>

#### errors on a negative serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=HOUR(-0.5)")).to_contain("#ERR")
expect(_eval("=MINUTE(-0.5)")).to_contain("#ERR")
expect(_eval("=SECOND(-0.5)")).to_contain("#ERR")
```

</details>

### Calc ISOWEEKNUM

#### matches the Excel docs example DATE(2012,3,9) -> 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISOWEEKNUM(DATE(2012,3,9))")).to_equal("10")
```

</details>

#### 2016-01-01 belongs to ISO week 53 of 2015

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISOWEEKNUM(DATE(2016,1,1))")).to_equal("53")
```

</details>

#### 2005-01-01 belongs to ISO week 53 of 2004

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISOWEEKNUM(DATE(2005,1,1))")).to_equal("53")
```

</details>

#### a mid-year Monday starts its own week (2026-07-06 -> 28)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISOWEEKNUM(DATE(2026,7,6))")).to_equal("28")
```

</details>

#### errors without an argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISOWEEKNUM()")).to_contain("#ERR")
```

</details>

### Calc DAYS360

#### matches the Excel docs example Jan 30 -> Feb 1 2011 = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DAYS360(DATE(2011,1,30),DATE(2011,2,1))")).to_equal("1")
```

</details>

#### US NASD treats end-of-February start as day 30

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DAYS360(DATE(2011,2,28),DATE(2011,3,31))")).to_equal("30")
```

</details>

#### European method (TRUE) clamps only day 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DAYS360(DATE(2011,2,28),DATE(2011,3,31),TRUE)")).to_equal("32")
```

</details>

#### a full civil year counts 360 days

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DAYS360(DATE(2011,1,1),DATE(2011,12,31))")).to_equal("360")
```

</details>

#### errors below 2 arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DAYS360(DATE(2011,1,1))")).to_contain("#ERR")
```

</details>

### Calc YEARFRAC

#### basis 0 (default, 30/360 US) = 209/360

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30))", 0.5805555556, 0.0000001)).to_be(true)
expect(_approx("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30),0)", 0.5805555556, 0.0000001)).to_be(true)
```

</details>

#### basis 1 (actual/actual, leap year) = 211/366

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30),1)", 0.5765027322, 0.0000001)).to_be(true)
```

</details>

#### basis 3 (actual/365) = 211/365 — brief said 0.575342, corrected

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30),3)", 0.5780821918, 0.0000001)).to_be(true)
```

</details>

#### basis 2 (actual/360) = 211/360

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30),2)", 0.5861111111, 0.0000001)).to_be(true)
```

</details>

#### returns the absolute fraction when start > end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_approx("=YEARFRAC(DATE(2012,7,30),DATE(2012,1,1),0)", 0.5805555556, 0.0000001)).to_be(true)
```

</details>

#### rejects a basis outside 0..4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30),9)")).to_contain("#ERR")
```

</details>

### Calc COMBINA / PERMUTATIONA

#### COMBINA(4,3) = C(6,3) = 20

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=COMBINA(4,3)")).to_equal("20")
```

</details>

#### COMBINA(10,3) = C(12,3) = 220

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=COMBINA(10,3)")).to_equal("220")
```

</details>

#### COMBINA(n,0) = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=COMBINA(4,0)")).to_equal("1")
```

</details>

#### COMBINA rejects negative n and zero n with positive k

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=COMBINA(-1,2)")).to_contain("#ERR")
expect(_eval("=COMBINA(0,3)")).to_contain("#ERR")
```

</details>

#### PERMUTATIONA(3,2) = 9 and PERMUTATIONA(2,3) = 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=PERMUTATIONA(3,2)")).to_equal("9")
expect(_eval("=PERMUTATIONA(2,3)")).to_equal("8")
```

</details>

#### PERMUTATIONA rejects negative arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=PERMUTATIONA(-3,2)")).to_contain("#ERR")
```

</details>

### Calc NETWORKDAYS.INTL

#### weekend 1 (Sat/Sun) matches NETWORKDAYS: Jul 1-10 2026 = 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),1)")).to_equal("8")
expect(_eval("=NETWORKDAYS(DATE(2026,7,1),DATE(2026,7,10))")).to_equal("8")
```

</details>

#### weekend 11 (Sunday only) counts 9 of the 10 days

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),11)")).to_equal("9")
```

</details>

#### weekend 7 (Fri/Sat) counts 7 of the 10 days

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),7)")).to_equal("7")
```

</details>

#### excludes a workday holiday (Fri Jul 3) -> 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),1,DATE(2026,7,3))")).to_equal("7")
```

</details>

#### negates when start is after end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,10),DATE(2026,7,1),1)")).to_equal("-8")
```

</details>

#### rejects weekend codes outside 1-7 / 11-17

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),8)")).to_contain("#ERR")
```

</details>

### Calc WORKDAY.INTL

#### weekend 1: Wed Jul 1 2026 + 5 workdays = Wed Jul 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=WORKDAY.INTL(DATE(2026,7,1),5,1)-DATE(2026,7,8)")).to_equal("0")
```

</details>

#### weekend 7 (Fri/Sat): Wed Jul 1 + 3 workdays = Mon Jul 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=WORKDAY.INTL(DATE(2026,7,1),3,7)-DATE(2026,7,6)")).to_equal("0")
```

</details>

#### steps backward for negative days: Fri Jul 10 - 3 = Tue Jul 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=WORKDAY.INTL(DATE(2026,7,10),-3,1)-DATE(2026,7,7)")).to_equal("0")
```

</details>

#### skips a holiday (Mon Jul 6) -> Thu Jul 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=WORKDAY.INTL(DATE(2026,7,1),5,1,DATE(2026,7,6))-DATE(2026,7,9)")).to_equal("0")
```

</details>

#### rejects weekend codes outside 1-7 / 11-17

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=WORKDAY.INTL(DATE(2026,7,1),5,0)")).to_contain("#ERR")
```

</details>

### Calc RAND / RANDBETWEEN

#### RAND() stays in [0,1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IF(AND(RAND()>=0,RAND()<1),1,0)")).to_equal("1")
```

</details>

#### RANDBETWEEN(5,5) is deterministically 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=RANDBETWEEN(5,5)")).to_equal("5")
```

</details>

#### RANDBETWEEN(1,10) stays in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IF(AND(RANDBETWEEN(1,10)>=1,RANDBETWEEN(1,10)<=10),1,0)")).to_equal("1")
```

</details>

#### RANDBETWEEN rejects bottom > top

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=RANDBETWEEN(10,1)")).to_contain("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
