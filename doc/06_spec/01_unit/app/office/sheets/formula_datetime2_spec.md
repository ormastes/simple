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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TIME(6,0,0) is 0.25
   - Expected: _eval("=TIME(6,0,0)") equals `0.25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TIME(6,0,0) is 0.25")
expect(_eval("=TIME(6,0,0)")).to_equal("0.25")
```

</details>

#### TIME(12,30,0) is 0.520833...

- TIME(12,30,0) is 0.520833...


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TIME(12,30,0) is 0.520833...")
expect(_approx("=TIME(12,30,0)", 0.5208333333, 0.0000001)).to_be(true)
```

</details>

#### wraps past midnight (TIME(27,0,0) = TIME(3,0,0))

- wraps past midnight (TIME(27,0,0) = TIME(3,0,0))
   - Expected: _eval("=TIME(27,0,0)=TIME(3,0,0)") equals `TRUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps past midnight (TIME(27,0,0) = TIME(3,0,0))")
expect(_eval("=TIME(27,0,0)=TIME(3,0,0)")).to_equal("TRUE")
```

</details>

#### rolls over oversized minutes (TIME(0,90,0) = TIME(1,30,0))

- rolls over oversized minutes (TIME(0,90,0) = TIME(1,30,0))
   - Expected: _eval("=TIME(0,90,0)=TIME(1,30,0)") equals `TRUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rolls over oversized minutes (TIME(0,90,0) = TIME(1,30,0))")
expect(_eval("=TIME(0,90,0)=TIME(1,30,0)")).to_equal("TRUE")
```

</details>

#### errors on negative components

- errors on negative components


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors on negative components")
expect(_eval("=TIME(-1,0,0)")).to_contain("#ERR")
```

</details>

#### errors below 3 arguments

- errors below 3 arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors below 3 arguments")
expect(_eval("=TIME(6,0)")).to_contain("#ERR")
```

</details>

### Calc TIMEVALUE

#### parses the Excel docs example 2:24 AM as 0.1

- parses the Excel docs example 2:24 AM as 0.1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the Excel docs example 2:24 AM as 0.1")
expect(_approx("=TIMEVALUE(\"2:24 AM\")", 0.1, 0.0000001)).to_be(true)
```

</details>

#### parses 6:00 AM as 0.25

- parses 6:00 AM as 0.25
   - Expected: _eval("=TIMEVALUE(\"6:00 AM\")") equals `0.25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses 6:00 AM as 0.25")
expect(_eval("=TIMEVALUE(\"6:00 AM\")")).to_equal("0.25")
```

</details>

#### parses 24-hour H:MM (14:30 = 0.604166...)

- parses 24-hour H:MM (14:30 = 0.604166...)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses 24-hour H:MM (14:30 = 0.604166...)")
expect(_approx("=TIMEVALUE(\"14:30\")", 0.6041666667, 0.0000001)).to_be(true)
```

</details>

#### parses H:MM:SS with PM (2:24:36 PM = 51876/86400)

- parses H:MM:SS with PM (2:24:36 PM = 51876/86400)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses H:MM:SS with PM (2:24:36 PM = 51876/86400)")
expect(_approx("=TIMEVALUE(\"2:24:36 PM\")", 0.6004166667, 0.0000001)).to_be(true)
```

</details>

#### 12 AM is midnight and 12:30 PM is 0.520833...

- 12 AM is midnight and 12:30 PM is 0.520833...
   - Expected: _eval("=TIMEVALUE(\"12:00 AM\")") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("12 AM is midnight and 12:30 PM is 0.520833...")
expect(_eval("=TIMEVALUE(\"12:00 AM\")")).to_equal("0")
expect(_approx("=TIMEVALUE(\"12:30 PM\")", 0.5208333333, 0.0000001)).to_be(true)
```

</details>

#### rejects unparseable text

- rejects unparseable text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unparseable text")
expect(_eval("=TIMEVALUE(\"banana\")")).to_contain("#ERR")
```

</details>

#### rejects out-of-range fields (25:00 and 7:75)

- rejects out-of-range fields (25:00 and 7:75)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects out-of-range fields (25:00 and 7:75)")
expect(_eval("=TIMEVALUE(\"25:00\")")).to_contain("#ERR")
expect(_eval("=TIMEVALUE(\"7:75\")")).to_contain("#ERR")
```

</details>

### Calc HOUR / MINUTE / SECOND

#### HOUR(0.75) is 18

- HOUR(0.75) is 18
   - Expected: _eval("=HOUR(0.75)") equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HOUR(0.75) is 18")
expect(_eval("=HOUR(0.75)")).to_equal("18")
```

</details>

#### HOUR(TIME(6,0,0)) is 6

- HOUR(TIME(6,0,0)) is 6
   - Expected: _eval("=HOUR(TIME(6,0,0))") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HOUR(TIME(6,0,0)) is 6")
expect(_eval("=HOUR(TIME(6,0,0))")).to_equal("6")
```

</details>

#### MINUTE(TIME(12,30,0)) is 30 (exact serial, not a truncated literal)

- MINUTE(TIME(12,30,0)) is 30 (exact serial, not a truncated literal)
   - Expected: _eval("=MINUTE(TIME(12,30,0))") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MINUTE(TIME(12,30,0)) is 30 (exact serial, not a truncated literal)")
expect(_eval("=MINUTE(TIME(12,30,0))")).to_equal("30")
```

</details>

#### SECOND(TIME(4,48,18)) is 18

- SECOND(TIME(4,48,18)) is 18
   - Expected: _eval("=SECOND(TIME(4,48,18))") equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SECOND(TIME(4,48,18)) is 18")
expect(_eval("=SECOND(TIME(4,48,18))")).to_equal("18")
```

</details>

#### ignores the whole-day part of a serial

- ignores the whole-day part of a serial
   - Expected: _eval("=HOUR(DATE(2026,7,1)+0.25)") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores the whole-day part of a serial")
expect(_eval("=HOUR(DATE(2026,7,1)+0.25)")).to_equal("6")
```

</details>

#### errors on a negative serial

- errors on a negative serial


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors on a negative serial")
expect(_eval("=HOUR(-0.5)")).to_contain("#ERR")
expect(_eval("=MINUTE(-0.5)")).to_contain("#ERR")
expect(_eval("=SECOND(-0.5)")).to_contain("#ERR")
```

</details>

### Calc ISOWEEKNUM

#### matches the Excel docs example DATE(2012,3,9) -> 10

- matches the Excel docs example DATE(2012,3,9) -> 10
   - Expected: _eval("=ISOWEEKNUM(DATE(2012,3,9))") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the Excel docs example DATE(2012,3,9) -> 10")
expect(_eval("=ISOWEEKNUM(DATE(2012,3,9))")).to_equal("10")
```

</details>

#### 2016-01-01 belongs to ISO week 53 of 2015

- 2016-01-01 belongs to ISO week 53 of 2015
   - Expected: _eval("=ISOWEEKNUM(DATE(2016,1,1))") equals `53`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2016-01-01 belongs to ISO week 53 of 2015")
expect(_eval("=ISOWEEKNUM(DATE(2016,1,1))")).to_equal("53")
```

</details>

#### 2005-01-01 belongs to ISO week 53 of 2004

- 2005-01-01 belongs to ISO week 53 of 2004
   - Expected: _eval("=ISOWEEKNUM(DATE(2005,1,1))") equals `53`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2005-01-01 belongs to ISO week 53 of 2004")
expect(_eval("=ISOWEEKNUM(DATE(2005,1,1))")).to_equal("53")
```

</details>

#### a mid-year Monday starts its own week (2026-07-06 -> 28)

- a mid-year Monday starts its own week (2026-07-06 -> 28)
   - Expected: _eval("=ISOWEEKNUM(DATE(2026,7,6))") equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a mid-year Monday starts its own week (2026-07-06 -> 28)")
expect(_eval("=ISOWEEKNUM(DATE(2026,7,6))")).to_equal("28")
```

</details>

#### errors without an argument

- errors without an argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors without an argument")
expect(_eval("=ISOWEEKNUM()")).to_contain("#ERR")
```

</details>

### Calc DAYS360

#### matches the Excel docs example Jan 30 -> Feb 1 2011 = 1

- matches the Excel docs example Jan 30 -> Feb 1 2011 = 1
   - Expected: _eval("=DAYS360(DATE(2011,1,30),DATE(2011,2,1))") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the Excel docs example Jan 30 -> Feb 1 2011 = 1")
expect(_eval("=DAYS360(DATE(2011,1,30),DATE(2011,2,1))")).to_equal("1")
```

</details>

#### US NASD treats end-of-February start as day 30

- US NASD treats end-of-February start as day 30
   - Expected: _eval("=DAYS360(DATE(2011,2,28),DATE(2011,3,31))") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("US NASD treats end-of-February start as day 30")
expect(_eval("=DAYS360(DATE(2011,2,28),DATE(2011,3,31))")).to_equal("30")
```

</details>

#### European method (TRUE) clamps only day 31

- European method (TRUE) clamps only day 31
   - Expected: _eval("=DAYS360(DATE(2011,2,28),DATE(2011,3,31),TRUE)") equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("European method (TRUE) clamps only day 31")
expect(_eval("=DAYS360(DATE(2011,2,28),DATE(2011,3,31),TRUE)")).to_equal("32")
```

</details>

#### a full civil year counts 360 days

- a full civil year counts 360 days
   - Expected: _eval("=DAYS360(DATE(2011,1,1),DATE(2011,12,31))") equals `360`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a full civil year counts 360 days")
expect(_eval("=DAYS360(DATE(2011,1,1),DATE(2011,12,31))")).to_equal("360")
```

</details>

#### errors below 2 arguments

- errors below 2 arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors below 2 arguments")
expect(_eval("=DAYS360(DATE(2011,1,1))")).to_contain("#ERR")
```

</details>

### Calc YEARFRAC

#### basis 0 (default, 30/360 US) = 209/360

- basis 0 (default, 30/360 US) = 209/360


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("basis 0 (default, 30/360 US) = 209/360")
expect(_approx("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30))", 0.5805555556, 0.0000001)).to_be(true)
expect(_approx("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30),0)", 0.5805555556, 0.0000001)).to_be(true)
```

</details>

#### basis 1 (actual/actual, leap year) = 211/366

- basis 1 (actual/actual, leap year) = 211/366


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("basis 1 (actual/actual, leap year) = 211/366")
expect(_approx("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30),1)", 0.5765027322, 0.0000001)).to_be(true)
```

</details>

#### basis 3 (actual/365) = 211/365 — brief said 0.575342, corrected

- basis 3 (actual/365) = 211/365 — brief said 0.575342, corrected


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("basis 3 (actual/365) = 211/365 — brief said 0.575342, corrected")
expect(_approx("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30),3)", 0.5780821918, 0.0000001)).to_be(true)
```

</details>

#### basis 2 (actual/360) = 211/360

- basis 2 (actual/360) = 211/360


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("basis 2 (actual/360) = 211/360")
expect(_approx("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30),2)", 0.5861111111, 0.0000001)).to_be(true)
```

</details>

#### returns the absolute fraction when start > end

- returns the absolute fraction when start > end


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the absolute fraction when start > end")
expect(_approx("=YEARFRAC(DATE(2012,7,30),DATE(2012,1,1),0)", 0.5805555556, 0.0000001)).to_be(true)
```

</details>

#### rejects a basis outside 0..4

- rejects a basis outside 0..4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a basis outside 0..4")
expect(_eval("=YEARFRAC(DATE(2012,1,1),DATE(2012,7,30),9)")).to_contain("#ERR")
```

</details>

### Calc COMBINA / PERMUTATIONA

#### COMBINA(4,3) = C(6,3) = 20

- COMBINA(4,3) = C(6,3) = 20
   - Expected: _eval("=COMBINA(4,3)") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COMBINA(4,3) = C(6,3) = 20")
expect(_eval("=COMBINA(4,3)")).to_equal("20")
```

</details>

#### COMBINA(10,3) = C(12,3) = 220

- COMBINA(10,3) = C(12,3) = 220
   - Expected: _eval("=COMBINA(10,3)") equals `220`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COMBINA(10,3) = C(12,3) = 220")
expect(_eval("=COMBINA(10,3)")).to_equal("220")
```

</details>

#### COMBINA(n,0) = 1

- COMBINA(n,0) = 1
   - Expected: _eval("=COMBINA(4,0)") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COMBINA(n,0) = 1")
expect(_eval("=COMBINA(4,0)")).to_equal("1")
```

</details>

#### COMBINA rejects negative n and zero n with positive k

- COMBINA rejects negative n and zero n with positive k


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COMBINA rejects negative n and zero n with positive k")
expect(_eval("=COMBINA(-1,2)")).to_contain("#ERR")
expect(_eval("=COMBINA(0,3)")).to_contain("#ERR")
```

</details>

#### PERMUTATIONA(3,2) = 9 and PERMUTATIONA(2,3) = 8

- PERMUTATIONA(3,2) = 9 and PERMUTATIONA(2,3) = 8
   - Expected: _eval("=PERMUTATIONA(3,2)") equals `9`
   - Expected: _eval("=PERMUTATIONA(2,3)") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERMUTATIONA(3,2) = 9 and PERMUTATIONA(2,3) = 8")
expect(_eval("=PERMUTATIONA(3,2)")).to_equal("9")
expect(_eval("=PERMUTATIONA(2,3)")).to_equal("8")
```

</details>

#### PERMUTATIONA rejects negative arguments

- PERMUTATIONA rejects negative arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERMUTATIONA rejects negative arguments")
expect(_eval("=PERMUTATIONA(-3,2)")).to_contain("#ERR")
```

</details>

### Calc NETWORKDAYS.INTL

#### weekend 1 (Sat/Sun) matches NETWORKDAYS: Jul 1-10 2026 = 8

- weekend 1 (Sat/Sun) matches NETWORKDAYS: Jul 1-10 2026 = 8
   - Expected: _eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),1)") equals `8`
   - Expected: _eval("=NETWORKDAYS(DATE(2026,7,1),DATE(2026,7,10))") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weekend 1 (Sat/Sun) matches NETWORKDAYS: Jul 1-10 2026 = 8")
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),1)")).to_equal("8")
expect(_eval("=NETWORKDAYS(DATE(2026,7,1),DATE(2026,7,10))")).to_equal("8")
```

</details>

#### weekend 11 (Sunday only) counts 9 of the 10 days

- weekend 11 (Sunday only) counts 9 of the 10 days
   - Expected: _eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),11)") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weekend 11 (Sunday only) counts 9 of the 10 days")
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),11)")).to_equal("9")
```

</details>

#### weekend 7 (Fri/Sat) counts 7 of the 10 days

- weekend 7 (Fri/Sat) counts 7 of the 10 days
   - Expected: _eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),7)") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weekend 7 (Fri/Sat) counts 7 of the 10 days")
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),7)")).to_equal("7")
```

</details>

#### excludes a workday holiday (Fri Jul 3) -> 7

- excludes a workday holiday (Fri Jul 3) -> 7
   - Expected: _eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),1,DATE(2026,7,3))") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes a workday holiday (Fri Jul 3) -> 7")
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),1,DATE(2026,7,3))")).to_equal("7")
```

</details>

#### negates when start is after end

- negates when start is after end
   - Expected: _eval("=NETWORKDAYS.INTL(DATE(2026,7,10),DATE(2026,7,1),1)") equals `-8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negates when start is after end")
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,10),DATE(2026,7,1),1)")).to_equal("-8")
```

</details>

#### rejects weekend codes outside 1-7 / 11-17

- rejects weekend codes outside 1-7 / 11-17


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects weekend codes outside 1-7 / 11-17")
expect(_eval("=NETWORKDAYS.INTL(DATE(2026,7,1),DATE(2026,7,10),8)")).to_contain("#ERR")
```

</details>

### Calc WORKDAY.INTL

#### weekend 1: Wed Jul 1 2026 + 5 workdays = Wed Jul 8

- weekend 1: Wed Jul 1 2026 + 5 workdays = Wed Jul 8
   - Expected: _eval("=WORKDAY.INTL(DATE(2026,7,1),5,1)-DATE(2026,7,8)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weekend 1: Wed Jul 1 2026 + 5 workdays = Wed Jul 8")
expect(_eval("=WORKDAY.INTL(DATE(2026,7,1),5,1)-DATE(2026,7,8)")).to_equal("0")
```

</details>

#### weekend 7 (Fri/Sat): Wed Jul 1 + 3 workdays = Mon Jul 6

- weekend 7 (Fri/Sat): Wed Jul 1 + 3 workdays = Mon Jul 6
   - Expected: _eval("=WORKDAY.INTL(DATE(2026,7,1),3,7)-DATE(2026,7,6)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("weekend 7 (Fri/Sat): Wed Jul 1 + 3 workdays = Mon Jul 6")
expect(_eval("=WORKDAY.INTL(DATE(2026,7,1),3,7)-DATE(2026,7,6)")).to_equal("0")
```

</details>

#### steps backward for negative days: Fri Jul 10 - 3 = Tue Jul 7

- steps backward for negative days: Fri Jul 10 - 3 = Tue Jul 7
   - Expected: _eval("=WORKDAY.INTL(DATE(2026,7,10),-3,1)-DATE(2026,7,7)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("steps backward for negative days: Fri Jul 10 - 3 = Tue Jul 7")
expect(_eval("=WORKDAY.INTL(DATE(2026,7,10),-3,1)-DATE(2026,7,7)")).to_equal("0")
```

</details>

#### skips a holiday (Mon Jul 6) -> Thu Jul 9

- skips a holiday (Mon Jul 6) -> Thu Jul 9
   - Expected: _eval("=WORKDAY.INTL(DATE(2026,7,1),5,1,DATE(2026,7,6))-DATE(2026,7,9)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips a holiday (Mon Jul 6) -> Thu Jul 9")
expect(_eval("=WORKDAY.INTL(DATE(2026,7,1),5,1,DATE(2026,7,6))-DATE(2026,7,9)")).to_equal("0")
```

</details>

#### rejects weekend codes outside 1-7 / 11-17

- rejects weekend codes outside 1-7 / 11-17


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects weekend codes outside 1-7 / 11-17")
expect(_eval("=WORKDAY.INTL(DATE(2026,7,1),5,0)")).to_contain("#ERR")
```

</details>

### Calc RAND / RANDBETWEEN

#### RAND() stays in [0,1)

- RAND() stays in [0,1)
   - Expected: _eval("=IF(AND(RAND()>=0,RAND()<1),1,0)") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RAND() stays in [0,1)")
expect(_eval("=IF(AND(RAND()>=0,RAND()<1),1,0)")).to_equal("1")
```

</details>

#### RANDBETWEEN(5,5) is deterministically 5

- RANDBETWEEN(5,5) is deterministically 5
   - Expected: _eval("=RANDBETWEEN(5,5)") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RANDBETWEEN(5,5) is deterministically 5")
expect(_eval("=RANDBETWEEN(5,5)")).to_equal("5")
```

</details>

#### RANDBETWEEN(1,10) stays in range

- RANDBETWEEN(1,10) stays in range
   - Expected: _eval("=IF(AND(RANDBETWEEN(1,10)>=1,RANDBETWEEN(1,10)<=10),1,0)") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RANDBETWEEN(1,10) stays in range")
expect(_eval("=IF(AND(RANDBETWEEN(1,10)>=1,RANDBETWEEN(1,10)<=10),1,0)")).to_equal("1")
```

</details>

#### RANDBETWEEN rejects bottom > top

- RANDBETWEEN rejects bottom > top


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RANDBETWEEN rejects bottom > top")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2047f6995053271a17a283001b53ad0655fdd87df388680cdafd6d2f922928dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2047f6995053271a17a283001b53ad0655fdd87df388680cdafd6d2f922928dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2047f6995053271a17a283001b53ad0655fdd87df388680cdafd6d2f922928dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_datetime2_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_datetime2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_datetime2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_datetime2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_datetime2_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TIME(6,0,0) is 0.25' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_datetime2_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TIME(12,30,0) is 0.520833...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_datetime2_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps past midnight (TIME(27,0,0) = TIME(3,0,0))' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
