# formula_math_spec

> Calc math/engineering functions spec — 15 additions toward Excel's set.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_math_spec

Calc math/engineering functions spec — 15 additions toward Excel's set.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_math_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc math/engineering functions spec — 15 additions toward Excel's set.

EXP/LN/LOG10 use pure-Simple series implementations; verified against known
values. GCD/LCM/FACT are integer-exact; EVEN/ODD/ROUNDUP round away from zero.

## Scenarios

### Calc math functions

#### EXP/LN/LOG10 match known values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- EXP/LN/LOG10 match known values
   - Expected: _eval("=LN(2.718281828459045)") equals `1`
   - Expected: _eval("=LOG10(1000)") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EXP/LN/LOG10 match known values")
expect(_eval("=EXP(1)")).to_start_with("2.71828")
expect(_eval("=LN(2.718281828459045)")).to_equal("1")
expect(_eval("=LOG10(1000)")).to_equal("3")
```

</details>

#### PI/DEGREES/RADIANS convert angles

- PI/DEGREES/RADIANS convert angles
   - Expected: _eval("=DEGREES(PI())") equals `180`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PI/DEGREES/RADIANS convert angles")
expect(_eval("=DEGREES(PI())")).to_equal("180")
expect(_eval("=RADIANS(180)")).to_start_with("3.14159")
```

</details>

#### FACT/GCD/LCM are integer-exact

- FACT/GCD/LCM are integer-exact
   - Expected: _eval("=FACT(5)") equals `120`
   - Expected: _eval("=GCD(12, 18)") equals `6`
   - Expected: _eval("=LCM(4, 6)") equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FACT/GCD/LCM are integer-exact")
expect(_eval("=FACT(5)")).to_equal("120")
expect(_eval("=GCD(12, 18)")).to_equal("6")
expect(_eval("=LCM(4, 6)")).to_equal("12")
```

</details>

#### SUMSQ/AVEDEV aggregate ranges

- SUMSQ/AVEDEV aggregate ranges
   - Expected: _eval("=SUMSQ(A1:A2)") equals `25`
   - Expected: _eval("=AVEDEV(A1:A2)") equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUMSQ/AVEDEV aggregate ranges")
expect(_eval("=SUMSQ(A1:A2)")).to_equal("25")
expect(_eval("=AVEDEV(A1:A2)")).to_equal("0.5")
```

</details>

#### EVEN/ODD/ROUNDUP/ROUNDDOWN round correctly

- EVEN/ODD/ROUNDUP/ROUNDDOWN round correctly
   - Expected: _eval("=EVEN(3.1)") equals `4`
   - Expected: _eval("=ODD(4)") equals `5`
   - Expected: _eval("=ROUNDUP(2.1)") equals `3`
   - Expected: _eval("=ROUNDDOWN(2.9)") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EVEN/ODD/ROUNDUP/ROUNDDOWN round correctly")
expect(_eval("=EVEN(3.1)")).to_equal("4")
expect(_eval("=ODD(4)")).to_equal("5")
expect(_eval("=ROUNDUP(2.1)")).to_equal("3")
expect(_eval("=ROUNDDOWN(2.9)")).to_equal("2")
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

- Canonical SPipe generation for source `759a1bd7c37e50dec3bf40655badf5207b63a53085b880f44c9ddeafff2eb192`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `759a1bd7c37e50dec3bf40655badf5207b63a53085b880f44c9ddeafff2eb192`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `759a1bd7c37e50dec3bf40655badf5207b63a53085b880f44c9ddeafff2eb192`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_math_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_math_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_math_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_math_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_math_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'EXP/LN/LOG10 match known values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_math_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PI/DEGREES/RADIANS convert angles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_math_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FACT/GCD/LCM are integer-exact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
