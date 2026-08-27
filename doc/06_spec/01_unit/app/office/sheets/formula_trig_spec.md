# formula_trig_spec

> Calc trigonometry/combinatorics spec — 15 additions (65 functions total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_trig_spec

Calc trigonometry/combinatorics spec — 15 additions (65 functions total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_trig_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc trigonometry/combinatorics spec — 15 additions (65 functions total).

SIN/COS/TAN/ASIN/ACOS/ATAN use pure-Simple series with range reduction;
verified against exact identities. Hyperbolics build on the EXP series.

## Scenarios

### Calc trigonometry

#### SIN/COS/TAN match identities

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SIN/COS/TAN match identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIN/COS/TAN match identities")
expect(_eval("=SIN(PI() / 2)")).to_start_with("1")
expect(_eval("=COS(0)")).to_start_with("1")
expect(_eval("=TAN(PI() / 4)")).to_start_with("0.9999")
```

</details>

#### inverse functions return known angles

- inverse functions return known angles


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inverse functions return known angles")
expect(_eval("=ATAN(1)")).to_start_with("0.78539")
expect(_eval("=ASIN(0.5)")).to_start_with("0.52359")
expect(_eval("=ACOS(0)")).to_start_with("1.57079")
```

</details>

#### hyperbolics build on EXP

- hyperbolics build on EXP
   - Expected: _eval("=TANH(0)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hyperbolics build on EXP")
expect(_eval("=SINH(1)")).to_start_with("1.17520")
expect(_eval("=TANH(0)")).to_equal("0")
```

</details>

### Calc combinatorics and rounding

#### LOG with base, COMBIN, PERMUT

- LOG with base, COMBIN, PERMUT
   - Expected: _eval("=LOG(8, 2)") equals `3`
   - Expected: _eval("=COMBIN(5, 2)") equals `10`
   - Expected: _eval("=PERMUT(5, 2)") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOG with base, COMBIN, PERMUT")
expect(_eval("=LOG(8, 2)")).to_equal("3")
expect(_eval("=COMBIN(5, 2)")).to_equal("10")
expect(_eval("=PERMUT(5, 2)")).to_equal("20")
```

</details>

#### QUOTIENT, MROUND, SQRTPI

- QUOTIENT, MROUND, SQRTPI
   - Expected: _eval("=QUOTIENT(17, 5)") equals `3`
   - Expected: _eval("=MROUND(13, 5)") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QUOTIENT, MROUND, SQRTPI")
expect(_eval("=QUOTIENT(17, 5)")).to_equal("3")
expect(_eval("=MROUND(13, 5)")).to_equal("15")
expect(_eval("=SQRTPI(1)")).to_start_with("1.77245")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `8fde5cc1eb40eb8d54f52d14eda2f2a0cad5c5d463f90049350fba73bd0a3d59`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8fde5cc1eb40eb8d54f52d14eda2f2a0cad5c5d463f90049350fba73bd0a3d59`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8fde5cc1eb40eb8d54f52d14eda2f2a0cad5c5d463f90049350fba73bd0a3d59`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_trig_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_trig_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_trig_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_trig_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_trig_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SIN/COS/TAN match identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_trig_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inverse functions return known angles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_trig_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hyperbolics build on EXP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
