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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc date functions spec — DATE/YEAR/MONTH/DAY/DAYS/WEEKDAY/EDATE (113 total).

Pure integer civil<->serial conversion (Hinnant's algorithms), Excel 1900
serial system. Anchors: 1970-01-01 = 25569, 2000-01-01 = 36526; WEEKDAY uses
Excel's default Sunday=1; EDATE clamps month-end (Jan 31 + 1mo = Feb 28).

## Scenarios

### Calc dates: serial conversion

#### matches known Excel serial anchors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches known Excel serial anchors
   - Expected: _eval("=DATE(1970, 1, 1)") equals `25569`
   - Expected: _eval("=DATE(2000, 1, 1)") equals `36526`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches known Excel serial anchors")
expect(_eval("=DATE(1970, 1, 1)")).to_equal("25569")
expect(_eval("=DATE(2000, 1, 1)")).to_equal("36526")
```

</details>

#### round-trips year/month/day through the serial

- round-trips year/month/day through the serial
   - Expected: _eval("=YEAR(DATE(2026, 7, 3))") equals `2026`
   - Expected: _eval("=MONTH(DATE(2026, 7, 3))") equals `7`
   - Expected: _eval("=DAY(DATE(2026, 7, 3))") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips year/month/day through the serial")
expect(_eval("=YEAR(DATE(2026, 7, 3))")).to_equal("2026")
expect(_eval("=MONTH(DATE(2026, 7, 3))")).to_equal("7")
expect(_eval("=DAY(DATE(2026, 7, 3))")).to_equal("3")
```

</details>

### Calc dates: arithmetic

#### DAYS subtracts serials and WEEKDAY uses Sunday=1

- DAYS subtracts serials and WEEKDAY uses Sunday=1
   - Expected: _eval("=DAYS(DATE(2026, 7, 3), DATE(2026, 6, 3))") equals `30`
   - Expected: _eval("=WEEKDAY(DATE(2026, 7, 3))") equals `6`
   - Expected: _eval("=WEEKDAY(DATE(2026, 7, 5))") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DAYS subtracts serials and WEEKDAY uses Sunday=1")
expect(_eval("=DAYS(DATE(2026, 7, 3), DATE(2026, 6, 3))")).to_equal("30")
expect(_eval("=WEEKDAY(DATE(2026, 7, 3))")).to_equal("6")
expect(_eval("=WEEKDAY(DATE(2026, 7, 5))")).to_equal("1")
```

</details>

#### EDATE shifts months and clamps month-end

- EDATE shifts months and clamps month-end
   - Expected: _eval("=DAY(EDATE(DATE(2026, 1, 31), 1))") equals `28`
   - Expected: _eval("=MONTH(EDATE(DATE(2026, 11, 15), 3))") equals `2`
   - Expected: _eval("=YEAR(EDATE(DATE(2026, 11, 15), 3))") equals `2027`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EDATE shifts months and clamps month-end")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `374dc0fe875c7f6505a0235c8f76d1c99f48fa4d40559b1060b2064efde51a8a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `374dc0fe875c7f6505a0235c8f76d1c99f48fa4d40559b1060b2064efde51a8a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `374dc0fe875c7f6505a0235c8f76d1c99f48fa4d40559b1060b2064efde51a8a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_date_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_date_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_date_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_date_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_date_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches known Excel serial anchors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_date_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips year/month/day through the serial' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_date_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DAYS subtracts serials and WEEKDAY uses Sunday=1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
