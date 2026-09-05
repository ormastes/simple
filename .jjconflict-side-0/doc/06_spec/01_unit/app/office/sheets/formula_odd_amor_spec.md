# formula_odd_amor_spec

> Calc odd-period and depreciation functions spec (CARD odd-amor).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_odd_amor_spec

Calc odd-period and depreciation functions spec (CARD odd-amor).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_odd_amor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc odd-period and depreciation functions spec (CARD odd-amor).

Odd-period securities pricing (ODDLPRICE, ODDFPRICE) and French depreciation
with prorated purchase periods (AMORLINC, AMORDEGRC). Every expected value is
recomputed by hand from the Excel-documented algorithms (probe math in the
session scratchpad). Date-order violations, bad frequency, and basis outside
0..4 fail closed with #ERR for all four functions.

Ground truths (hand recomputation, all matching the Excel doc examples):
- ODDLPRICE 2008-02-07 / 2008-06-15 / last 2007-10-15, 3.75%/4.05%, freq 2,
  basis 0: quasi periods Oct15->Apr15->Oct15; sum DC/NL = 1 + 60/180,
  sum DSC/NL = 128/180, sum A/NL = 112/180 ->
  102.5/1.0144 - 1.166667 = 99.87828.
- ODDFPRICE 2008-11-11 / 2021-03-01, issue 2008-10-15, first coupon
  2009-03-01, 7.85%/6.25%, freq 2, basis 1: E=181, DSC=110, DFC=137, A=27,
  N=25 -> 46.8961 + 2.9158 + 64.3723 - 0.5855 = 113.5987 (doc: 113.598).
  SHORT odd first period only; issue more than one quasi period before the
  first coupon is rejected (documented ceiling).
- AMORLINC(2400, 2008-08-19, 2008-12-31, 300, p, 0.15, 1): period 0 is the
  PRORATED purchase period = 2400*0.15*134/366 = 131.8033; period 1 is the
  first FULL period = 2400*0.15 = 360 (Excel doc); full periods run through
  period 5; period 6 gets the remainder 2100 - 1800 - 131.8033 = 168.1967;
  period 7+ -> 0.
- AMORDEGRC same instrument: life 1/0.15 = 6.67y -> coefficient 2.5, so the
  degressive rate is 0.375. Period 0 = ROUND(2400*0.375*134/366) = 330;
  book 2070 -> period 1 = ROUND(776.25) = 776 (Excel doc); period 2 =
  ROUND(0.375*1294) = 485; when remaining passes salvage the last period
  takes half the book (period 5 = ROUND(316*0.5) = 158) and later periods
  are 0.

## Scenarios

### Calc odd-period securities — ODDLPRICE

#### ODDLPRICE prices a bond with odd last coupon period (Excel doc 99.87829)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ODDLPRICE prices a bond with odd last coupon period (Excel doc 99.87829)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ODDLPRICE prices a bond with odd last coupon period (Excel doc 99.87829)")
expect(_eval("=ODDLPRICE(DATE(2008,2,7), DATE(2008,6,15), DATE(2007,10,15), 0.0375, 0.0405, 100, 2, 0)")).to_start_with("99.8782")
```

</details>

#### ODDLPRICE with basis 1 (actual/actual) produces a finite price

- ODDLPRICE with basis 1 (actual/actual) produces a finite price


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ODDLPRICE with basis 1 (actual/actual) produces a finite price")
expect(_eval("=ODDLPRICE(DATE(2008,1,15), DATE(2008,12,15), DATE(2007,6,15), 0.05, 0.06, 100, 2, 1)")).to_contain(".")
```

</details>

#### rejects settlement >= maturity

- rejects settlement >= maturity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects settlement >= maturity")
expect(_eval("=ODDLPRICE(DATE(2008,6,15), DATE(2008,2,7), DATE(2007,10,15), 0.0375, 0.0405, 100, 2, 0)")).to_contain("#ERR")
```

</details>

#### rejects settlement <= last_interest

- rejects settlement <= last_interest


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects settlement <= last_interest")
expect(_eval("=ODDLPRICE(DATE(2007,10,15), DATE(2008,6,15), DATE(2007,10,15), 0.0375, 0.0405, 100, 2, 0)")).to_contain("#ERR")
```

</details>

#### rejects invalid frequency

- rejects invalid frequency


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid frequency")
expect(_eval("=ODDLPRICE(DATE(2008,2,7), DATE(2008,6,15), DATE(2007,10,15), 0.0375, 0.0405, 100, 3, 0)")).to_contain("#ERR")
```

</details>

#### rejects basis outside 0..4

- rejects basis outside 0..4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects basis outside 0..4")
expect(_eval("=ODDLPRICE(DATE(2008,2,7), DATE(2008,6,15), DATE(2007,10,15), 0.0375, 0.0405, 100, 2, 5)")).to_contain("#ERR")
```

</details>

#### rejects negative rate

- rejects negative rate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative rate")
expect(_eval("=ODDLPRICE(DATE(2008,2,7), DATE(2008,6,15), DATE(2007,10,15), -0.0375, 0.0405, 100, 2, 0)")).to_contain("#ERR")
```

</details>

#### rejects negative yield

- rejects negative yield


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative yield")
expect(_eval("=ODDLPRICE(DATE(2008,2,7), DATE(2008,6,15), DATE(2007,10,15), 0.0375, -0.0405, 100, 2, 0)")).to_contain("#ERR")
```

</details>

#### rejects non-positive redemption

- rejects non-positive redemption


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-positive redemption")
expect(_eval("=ODDLPRICE(DATE(2008,2,7), DATE(2008,6,15), DATE(2007,10,15), 0.0375, 0.0405, 0, 2, 0)")).to_contain("#ERR")
```

</details>

### Calc odd-period securities — ODDFPRICE

#### ODDFPRICE prices a bond with short odd first coupon (Excel doc 113.598)

- ODDFPRICE prices a bond with short odd first coupon (Excel doc 113.598)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ODDFPRICE prices a bond with short odd first coupon (Excel doc 113.598)")
expect(_eval("=ODDFPRICE(DATE(2008,11,11), DATE(2021,3,1), DATE(2008,10,15), DATE(2009,3,1), 0.0785, 0.0625, 100, 2, 1)")).to_start_with("113.59")
```

</details>

#### ODDFPRICE with basis 0 (30/360) produces a finite price

- ODDFPRICE with basis 0 (30/360) produces a finite price


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ODDFPRICE with basis 0 (30/360) produces a finite price")
expect(_eval("=ODDFPRICE(DATE(2008,11,11), DATE(2021,3,1), DATE(2008,10,15), DATE(2009,3,1), 0.0785, 0.0625, 100, 2, 0)")).to_contain(".")
```

</details>

#### rejects a LONG odd first period (documented ceiling)

- rejects a LONG odd first period (documented ceiling)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a LONG odd first period (documented ceiling)")
# Issue 2008-06-01 is more than one semi-annual quasi period
# (2008-09-01) before the 2009-03-01 first coupon.
expect(_eval("=ODDFPRICE(DATE(2008,11,11), DATE(2021,3,1), DATE(2008,6,1), DATE(2009,3,1), 0.0785, 0.0625, 100, 2, 1)")).to_contain("#ERR")
```

</details>

#### rejects first_coupon <= settlement

- rejects first_coupon <= settlement


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects first_coupon <= settlement")
expect(_eval("=ODDFPRICE(DATE(2009,3,1), DATE(2021,3,1), DATE(2008,10,15), DATE(2009,3,1), 0.0785, 0.0625, 100, 2, 0)")).to_contain("#ERR")
```

</details>

#### rejects settlement <= issue

- rejects settlement <= issue


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects settlement <= issue")
expect(_eval("=ODDFPRICE(DATE(2008,10,15), DATE(2021,3,1), DATE(2008,10,15), DATE(2009,3,1), 0.0785, 0.0625, 100, 2, 0)")).to_contain("#ERR")
```

</details>

#### rejects maturity <= first_coupon

- rejects maturity <= first_coupon


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects maturity <= first_coupon")
expect(_eval("=ODDFPRICE(DATE(2008,11,11), DATE(2009,3,1), DATE(2008,10,15), DATE(2009,3,1), 0.0785, 0.0625, 100, 2, 0)")).to_contain("#ERR")
```

</details>

#### rejects invalid frequency

- rejects invalid frequency


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid frequency")
expect(_eval("=ODDFPRICE(DATE(2008,11,11), DATE(2021,3,1), DATE(2008,10,15), DATE(2009,3,1), 0.0785, 0.0625, 100, 3, 0)")).to_contain("#ERR")
```

</details>

#### rejects basis outside 0..4

- rejects basis outside 0..4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects basis outside 0..4")
expect(_eval("=ODDFPRICE(DATE(2008,11,11), DATE(2021,3,1), DATE(2008,10,15), DATE(2009,3,1), 0.0785, 0.0625, 100, 2, 5)")).to_contain("#ERR")
```

</details>

### Calc depreciation — AMORLINC (straight-line)

#### period 0 is the prorated purchase period (2400*0.15*134/366)

- period 0 is the prorated purchase period (2400*0.15*134/366)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("period 0 is the prorated purchase period (2400*0.15*134/366)")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 0, 0.15, 1)")).to_start_with("131.80")
```

</details>

#### period 1 is the first FULL period = cost*rate = 360 (Excel doc)

- period 1 is the first FULL period = cost*rate = 360 (Excel doc)
   - Expected: _eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 0.15, 1)") equals `360`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("period 1 is the first FULL period = cost*rate = 360 (Excel doc)")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 0.15, 1)")).to_equal("360")
```

</details>

#### period 2 is another full period (360)

- period 2 is another full period (360)
   - Expected: _eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 2, 0.15, 1)") equals `360`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("period 2 is another full period (360)")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 2, 0.15, 1)")).to_equal("360")
```

</details>

#### the period after the last full one takes the remainder to salvage

- the period after the last full one takes the remainder to salvage


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the period after the last full one takes the remainder to salvage")
# 2100 - 5*360 - 131.8033 = 168.1967
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 6, 0.15, 1)")).to_start_with("168.19")
```

</details>

#### periods past full depreciation are 0

- periods past full depreciation are 0
   - Expected: _eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 7, 0.15, 1)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("periods past full depreciation are 0")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 7, 0.15, 1)")).to_equal("0")
```

</details>

#### period 0 with basis 0 (30/360): 132/360 of a year -> exactly 132

- period 0 with basis 0 (30/360): 132/360 of a year -> exactly 132
   - Expected: _eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 0, 0.15, 0)") equals `132`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("period 0 with basis 0 (30/360): 132/360 of a year -> exactly 132")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 0, 0.15, 0)")).to_equal("132")
```

</details>

#### remainder period with basis 0 is exact: 2100 - 5*360 - 132 = 168

- remainder period with basis 0 is exact: 2100 - 5*360 - 132 = 168
   - Expected: _eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 6, 0.15, 0)") equals `168`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remainder period with basis 0 is exact: 2100 - 5*360 - 132 = 168")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 6, 0.15, 0)")).to_equal("168")
```

</details>

#### rejects negative cost

- rejects negative cost


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative cost")
expect(_eval("=AMORLINC(-2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 0.15, 1)")).to_contain("#ERR")
```

</details>

#### rejects salvage >= cost

- rejects salvage >= cost


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects salvage >= cost")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 2400, 1, 0.15, 1)")).to_contain("#ERR")
```

</details>

#### rejects negative rate

- rejects negative rate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative rate")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, -0.15, 1)")).to_contain("#ERR")
```

</details>

#### rejects rate > 1.0

- rejects rate > 1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects rate > 1.0")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 1.5, 1)")).to_contain("#ERR")
```

</details>

#### rejects negative period (period 0 is valid in Excel)

- rejects negative period (period 0 is valid in Excel)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative period (period 0 is valid in Excel)")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, -1, 0.15, 1)")).to_contain("#ERR")
```

</details>

#### rejects first_period <= date_purchased

- rejects first_period <= date_purchased


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects first_period <= date_purchased")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,8,19), 300, 1, 0.15, 1)")).to_contain("#ERR")
```

</details>

#### rejects basis outside 0..4

- rejects basis outside 0..4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects basis outside 0..4")
expect(_eval("=AMORLINC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 0.15, 5)")).to_contain("#ERR")
```

</details>

### Calc depreciation — AMORDEGRC (degressive)

#### period 0 is the prorated purchase period, rounded (330)

- period 0 is the prorated purchase period, rounded (330)
   - Expected: _eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 0, 0.15, 1)") equals `330`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("period 0 is the prorated purchase period, rounded (330)")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 0, 0.15, 1)")).to_equal("330")
```

</details>

#### period 1 applies the 2.5 coefficient to the reduced book = 776 (Excel doc)

- period 1 applies the 2.5 coefficient to the reduced book = 776 (Excel doc)
   - Expected: _eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 0.15, 1)") equals `776`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("period 1 applies the 2.5 coefficient to the reduced book = 776 (Excel doc)")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 0.15, 1)")).to_equal("776")
```

</details>

#### period 2 continues the degressive schedule (485)

- period 2 continues the degressive schedule (485)
   - Expected: _eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 2, 0.15, 1)") equals `485`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("period 2 continues the degressive schedule (485)")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 2, 0.15, 1)")).to_equal("485")
```

</details>

#### the closing period takes half the remaining book (158)

- the closing period takes half the remaining book (158)
   - Expected: _eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 5, 0.15, 1)") equals `158`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the closing period takes half the remaining book (158)")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 5, 0.15, 1)")).to_equal("158")
```

</details>

#### periods past full depreciation are 0

- periods past full depreciation are 0
   - Expected: _eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 6, 0.15, 1)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("periods past full depreciation are 0")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 6, 0.15, 1)")).to_equal("0")
```

</details>

#### period 1 with basis 0 (30/360) also lands on 776

- period 1 with basis 0 (30/360) also lands on 776
   - Expected: _eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 0.15, 0)") equals `776`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("period 1 with basis 0 (30/360) also lands on 776")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 0.15, 0)")).to_equal("776")
```

</details>

#### rejects negative cost

- rejects negative cost


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative cost")
expect(_eval("=AMORDEGRC(-2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 0.15, 1)")).to_contain("#ERR")
```

</details>

#### rejects salvage >= cost

- rejects salvage >= cost


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects salvage >= cost")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 2400, 1, 0.15, 1)")).to_contain("#ERR")
```

</details>

#### rejects negative rate

- rejects negative rate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative rate")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, -0.15, 1)")).to_contain("#ERR")
```

</details>

#### rejects rate > 1.0

- rejects rate > 1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects rate > 1.0")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 1.5, 1)")).to_contain("#ERR")
```

</details>

#### rejects negative period (period 0 is valid in Excel)

- rejects negative period (period 0 is valid in Excel)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative period (period 0 is valid in Excel)")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, -1, 0.15, 1)")).to_contain("#ERR")
```

</details>

#### rejects first_period <= date_purchased

- rejects first_period <= date_purchased


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects first_period <= date_purchased")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,8,19), 300, 1, 0.15, 1)")).to_contain("#ERR")
```

</details>

#### rejects basis outside 0..4

- rejects basis outside 0..4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects basis outside 0..4")
expect(_eval("=AMORDEGRC(2400, DATE(2008,8,19), DATE(2008,12,31), 300, 1, 0.15, 5)")).to_contain("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
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

- Canonical SPipe generation for source `5d4a3fc35c782f2a45562bcdb2a69a3671f39b108544a1db46e2e81fda87cb3e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d4a3fc35c782f2a45562bcdb2a69a3671f39b108544a1db46e2e81fda87cb3e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d4a3fc35c782f2a45562bcdb2a69a3671f39b108544a1db46e2e81fda87cb3e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_odd_amor_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_odd_amor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_odd_amor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_odd_amor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_odd_amor_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ODDLPRICE prices a bond with odd last coupon period (Excel doc 99.87829)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_odd_amor_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ODDLPRICE with basis 1 (actual/actual) produces a finite price' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_odd_amor_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects settlement >= maturity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
