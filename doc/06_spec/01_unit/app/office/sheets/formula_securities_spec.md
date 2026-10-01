# formula_securities_spec

> Calc financial-securities functions spec (CARD 3).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_securities_spec

Calc financial-securities functions spec (CARD 3).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_securities_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc financial-securities functions spec (CARD 3).

Day-count-basis + coupon-date machinery driving the fixed-income batch:
ACCRINT/ACCRINTM, the COUP* coupon-date family, PRICE/YIELD, PRICEDISC/
YIELDDISC, PRICEMAT/YIELDMAT, DISC/INTRATE/RECEIVED, DURATION/MDURATION,
the TBILL* treasury-bill trio and DOLLARDE/DOLLARFR. Every expected value is
recomputed against Excel-documented examples (probe in the session
scratchpad); fractional discounting routes through the exp/ln power helper.
Fail-closed #ERR domains (settle>=maturity, basis outside 0..4, freq not in
{1,2,4}, nonpositive price/redemption) are exercised.

Correction flagged during the probe: MDURATION of the DURATION instrument is
5.735670 (= 5.993775 / 1.045), NOT the plan's 5.73634; and YIELD's documented
instrument matures 2016-11-15 (yield 0.065 at price 95.04287) — the plan's
2017-11-15 maturity yields 0.064410, so the task-brief 2016 date is authoritative.

## Scenarios

### Calc securities — day-count / coupon machinery

#### COUPDAYS/COUPDAYBS/COUPDAYSNC split the actual coupon period (basis 1)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- COUPDAYS/COUPDAYBS/COUPDAYSNC split the actual coupon period (basis 1)
   - Expected: _eval("=COUPDAYS(DATE(2011,1,25), DATE(2011,11,15), 2, 1)") equals `181`
   - Expected: _eval("=COUPDAYBS(DATE(2011,1,25), DATE(2011,11,15), 2, 1)") equals `71`
   - Expected: _eval("=COUPDAYSNC(DATE(2011,1,25), DATE(2011,11,15), 2, 1)") equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COUPDAYS/COUPDAYBS/COUPDAYSNC split the actual coupon period (basis 1)")
expect(_eval("=COUPDAYS(DATE(2011,1,25), DATE(2011,11,15), 2, 1)")).to_equal("181")
expect(_eval("=COUPDAYBS(DATE(2011,1,25), DATE(2011,11,15), 2, 1)")).to_equal("71")
expect(_eval("=COUPDAYSNC(DATE(2011,1,25), DATE(2011,11,15), 2, 1)")).to_equal("110")
```

</details>

#### COUPNUM counts remaining coupons inclusive of maturity

- COUPNUM counts remaining coupons inclusive of maturity
   - Expected: _eval("=COUPNUM(DATE(2007,1,25), DATE(2008,11,15), 2, 1)") equals `4`
   - Expected: _eval("=COUPNUM(DATE(2011,1,25), DATE(2011,11,15), 2, 1)") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COUPNUM counts remaining coupons inclusive of maturity")
expect(_eval("=COUPNUM(DATE(2007,1,25), DATE(2008,11,15), 2, 1)")).to_equal("4")
expect(_eval("=COUPNUM(DATE(2011,1,25), DATE(2011,11,15), 2, 1)")).to_equal("2")
```

</details>

#### COUPPCD/COUPNCD walk to the straddling coupon dates

- COUPPCD/COUPNCD walk to the straddling coupon dates
   - Expected: _eval("=COUPPCD(DATE(2011,1,25), DATE(2011,11,15), 2, 1)") equals `40497`
   - Expected: _eval("=COUPNCD(DATE(2011,1,25), DATE(2011,11,15), 2, 1)") equals `40678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COUPPCD/COUPNCD walk to the straddling coupon dates")
expect(_eval("=COUPPCD(DATE(2011,1,25), DATE(2011,11,15), 2, 1)")).to_equal("40497")
expect(_eval("=COUPNCD(DATE(2011,1,25), DATE(2011,11,15), 2, 1)")).to_equal("40678")
```

</details>

### Calc securities — price and yield

#### PRICE discounts coupons + redemption on a 30/360 basis

- PRICE discounts coupons + redemption on a 30/360 basis


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PRICE discounts coupons + redemption on a 30/360 basis")
expect(_eval("=PRICE(DATE(2008,2,15), DATE(2017,11,15), 0.0575, 0.065, 100, 2, 0)")).to_start_with("94.6343")
```

</details>

#### YIELD inverts PRICE via bisection to the documented rate

- YIELD inverts PRICE via bisection to the documented rate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("YIELD inverts PRICE via bisection to the documented rate")
expect(_eval("=YIELD(DATE(2008,2,15), DATE(2016,11,15), 0.0575, 95.04287, 100, 2, 0)")).to_start_with("0.065")
```

</details>

#### PRICEDISC and YIELDDISC round-trip a discounted (zero-coupon) note

- PRICEDISC and YIELDDISC round-trip a discounted (zero-coupon) note


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PRICEDISC and YIELDDISC round-trip a discounted (zero-coupon) note")
expect(_eval("=PRICEDISC(DATE(2008,2,16), DATE(2008,3,1), 0.0525, 100, 2)")).to_start_with("99.7958")
expect(_eval("=YIELDDISC(DATE(2008,2,16), DATE(2008,3,1), 99.795, 100, 2)")).to_start_with("0.05282")
```

</details>

#### PRICEMAT and YIELDMAT round-trip an interest-at-maturity note

- PRICEMAT and YIELDMAT round-trip an interest-at-maturity note


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PRICEMAT and YIELDMAT round-trip an interest-at-maturity note")
expect(_eval("=PRICEMAT(DATE(2008,2,15), DATE(2008,4,13), DATE(2007,11,11), 0.061, 0.061, 0)")).to_start_with("99.9844")
expect(_eval("=YIELDMAT(DATE(2008,2,15), DATE(2008,4,13), DATE(2007,11,11), 0.061, 99.98449887555694, 0)")).to_start_with("0.061")
```

</details>

### Calc securities — accrued interest

#### ACCRINT accrues from issue to settlement

- ACCRINT accrues from issue to settlement


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ACCRINT accrues from issue to settlement")
expect(_eval("=ACCRINT(DATE(2008,3,1), DATE(2008,8,31), DATE(2008,5,1), 0.1, 1000, 2, 0)")).to_start_with("16.6666")
```

</details>

#### ACCRINTM accrues to maturity for a single-period note

- ACCRINTM accrues to maturity for a single-period note


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ACCRINTM accrues to maturity for a single-period note")
expect(_eval("=ACCRINTM(DATE(2008,4,1), DATE(2008,6,15), 0.1, 1000, 0)")).to_start_with("20.555")
```

</details>

### Calc securities — discount / rate / received

#### DISC recovers the discount rate

- DISC recovers the discount rate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DISC recovers the discount rate")
expect(_eval("=DISC(DATE(2007,1,25), DATE(2007,6,15), 97.975, 100, 1)")).to_start_with("0.05242")
```

</details>

#### INTRATE recovers the fully-invested interest rate

- INTRATE recovers the fully-invested interest rate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("INTRATE recovers the fully-invested interest rate")
expect(_eval("=INTRATE(DATE(2008,2,15), DATE(2008,5,15), 1000000, 1014420, 2)")).to_start_with("0.05768")
```

</details>

#### RECEIVED grosses up a discounted investment

- RECEIVED grosses up a discounted investment


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RECEIVED grosses up a discounted investment")
expect(_eval("=RECEIVED(DATE(2008,2,15), DATE(2008,5,15), 1000000, 0.0575, 2)")).to_start_with("1014584.6")
```

</details>

### Calc securities — duration

#### DURATION is the Macaulay duration in years

- DURATION is the Macaulay duration in years


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DURATION is the Macaulay duration in years")
expect(_eval("=DURATION(DATE(2008,1,1), DATE(2016,1,1), 0.08, 0.09, 2, 1)")).to_start_with("5.99377")
```

</details>

#### MDURATION is DURATION discounted by one periodic yield

- MDURATION is DURATION discounted by one periodic yield


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MDURATION is DURATION discounted by one periodic yield")
expect(_eval("=MDURATION(DATE(2008,1,1), DATE(2016,1,1), 0.08, 0.09, 2, 1)")).to_start_with("5.7356")
```

</details>

### Calc securities — treasury bills and fractional dollars

#### TBILLPRICE and TBILLYIELD round-trip a T-bill

- TBILLPRICE and TBILLYIELD round-trip a T-bill
   - Expected: _eval("=TBILLPRICE(DATE(2008,3,31), DATE(2008,6,1), 0.09)") equals `98.45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TBILLPRICE and TBILLYIELD round-trip a T-bill")
expect(_eval("=TBILLPRICE(DATE(2008,3,31), DATE(2008,6,1), 0.09)")).to_equal("98.45")
expect(_eval("=TBILLYIELD(DATE(2008,3,31), DATE(2008,6,1), 98.45)")).to_start_with("0.09141")
```

</details>

#### TBILLEQ gives the bond-equivalent yield

- TBILLEQ gives the bond-equivalent yield


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TBILLEQ gives the bond-equivalent yield")
expect(_eval("=TBILLEQ(DATE(2008,3,31), DATE(2008,6,1), 0.0914)")).to_start_with("0.09415")
```

</details>

#### DOLLARDE and DOLLARFR convert fractional <-> decimal dollars

- DOLLARDE and DOLLARFR convert fractional <-> decimal dollars
   - Expected: _eval("=DOLLARDE(1.02, 16)") equals `1.125`
   - Expected: _eval("=DOLLARFR(1.125, 16)") equals `1.02`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DOLLARDE and DOLLARFR convert fractional <-> decimal dollars")
expect(_eval("=DOLLARDE(1.02, 16)")).to_equal("1.125")
expect(_eval("=DOLLARFR(1.125, 16)")).to_equal("1.02")
```

</details>

### Calc securities — fail-closed domains

#### rejects settlement on or after maturity

- rejects settlement on or after maturity


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects settlement on or after maturity")
expect(_eval("=PRICE(DATE(2017,1,1), DATE(2008,1,1), 0.0575, 0.065, 100, 2, 0)")).to_contain("#ERR")
expect(_eval("=COUPNUM(DATE(2011,11,15), DATE(2011,1,25), 2, 1)")).to_contain("#ERR")
```

</details>

#### rejects a day-count basis outside 0..4

- rejects a day-count basis outside 0..4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a day-count basis outside 0..4")
expect(_eval("=COUPDAYS(DATE(2011,1,25), DATE(2011,11,15), 2, 5)")).to_contain("#ERR")
expect(_eval("=DISC(DATE(2007,1,25), DATE(2007,6,15), 97.975, 100, 9)")).to_contain("#ERR")
```

</details>

#### rejects a coupon frequency not in {1,2,4}

- rejects a coupon frequency not in {1,2,4}


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a coupon frequency not in {1,2,4}")
expect(_eval("=COUPNUM(DATE(2007,1,25), DATE(2008,11,15), 3, 1)")).to_contain("#ERR")
expect(_eval("=PRICE(DATE(2008,2,15), DATE(2017,11,15), 0.0575, 0.065, 100, 3, 0)")).to_contain("#ERR")
```

</details>

#### rejects nonpositive redemption / price

- rejects nonpositive redemption / price


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects nonpositive redemption / price")
expect(_eval("=DISC(DATE(2007,1,25), DATE(2007,6,15), 97.975, 0, 1)")).to_contain("#ERR")
expect(_eval("=YIELD(DATE(2008,2,15), DATE(2016,11,15), 0.0575, 0, 100, 2, 0)")).to_contain("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `b08a33a26e8194c62d58416e68907c5016a667b913b42fda4f2a18cf868ad25a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b08a33a26e8194c62d58416e68907c5016a667b913b42fda4f2a18cf868ad25a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b08a33a26e8194c62d58416e68907c5016a667b913b42fda4f2a18cf868ad25a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_securities_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_securities_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_securities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_securities_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_securities_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'COUPDAYS/COUPDAYBS/COUPDAYSNC split the actual coupon period (basis 1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_securities_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'COUPNUM counts remaining coupons inclusive of maturity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_securities_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'COUPPCD/COUPNCD walk to the straddling coupon dates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
