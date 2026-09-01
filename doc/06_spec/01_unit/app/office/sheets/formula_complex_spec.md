# formula_complex_spec

> Calc complex-number + clock functions spec (123 total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_complex_spec

Calc complex-number + clock functions spec (123 total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_complex_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc complex-number + clock functions spec (123 total).

Complex values are Excel-style text ("3+4i"); arithmetic verified against
hand-computed products/sums; IMABS on the 3-4-5 triangle. TODAY/NOW read the
runtime clock (UTC serial — local-tz offset is a recorded ceiling), asserted
structurally against the date pack.

## Scenarios

### Calc complex numbers

#### formats and parses Excel-style complex text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats and parses Excel-style complex text
   - Expected: _eval("=COMPLEX(3, 4)") equals `3+4i`
   - Expected: _eval("=COMPLEX(3, -4)") equals `3-4i`
   - Expected: _eval("=COMPLEX(0, 4)") equals `4i`
   - Expected: _eval("=IMREAL(\"-2-5i\")") equals `-2`
   - Expected: _eval("=IMAGINARY(\"-2-5i\")") equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats and parses Excel-style complex text")
expect(_eval("=COMPLEX(3, 4)")).to_equal("3+4i")
expect(_eval("=COMPLEX(3, -4)")).to_equal("3-4i")
expect(_eval("=COMPLEX(0, 4)")).to_equal("4i")
expect(_eval("=IMREAL(\"-2-5i\")")).to_equal("-2")
expect(_eval("=IMAGINARY(\"-2-5i\")")).to_equal("-5")
```

</details>

#### computes modulus, conjugate, sum, difference, product

- computes modulus, conjugate, sum, difference, product
   - Expected: _eval("=IMABS(\"3+4i\")") equals `5`
   - Expected: _eval("=IMCONJUGATE(\"3+4i\")") equals `3-4i`
   - Expected: _eval("=IMSUM(\"3+4i\", \"1-2i\")") equals `4+2i`
   - Expected: _eval("=IMSUB(\"3+4i\", \"1-2i\")") equals `2+6i`
   - Expected: _eval("=IMPRODUCT(\"1+2i\", \"3+4i\")") equals `-5+10i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes modulus, conjugate, sum, difference, product")
expect(_eval("=IMABS(\"3+4i\")")).to_equal("5")
expect(_eval("=IMCONJUGATE(\"3+4i\")")).to_equal("3-4i")
expect(_eval("=IMSUM(\"3+4i\", \"1-2i\")")).to_equal("4+2i")
expect(_eval("=IMSUB(\"3+4i\", \"1-2i\")")).to_equal("2+6i")
expect(_eval("=IMPRODUCT(\"1+2i\", \"3+4i\")")).to_equal("-5+10i")
```

</details>

### Calc clock functions

#### TODAY returns a serial consistent with the date pack

- TODAY returns a serial consistent with the date pack


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TODAY returns a serial consistent with the date pack")
val today = _eval("=TODAY()")
val year = _eval("=YEAR(TODAY())")
expect(today.to_f64() > 46000.0).to_be(true)
expect(year.to_f64() >= 2026.0).to_be(true)
```

</details>

#### NOW is TODAY plus a day fraction

- NOW is TODAY plus a day fraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NOW is TODAY plus a day fraction")
val diff = _eval("=NOW() - TODAY()")
expect(diff.to_f64() >= 0.0).to_be(true)
expect(diff.to_f64() < 1.0).to_be(true)
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

- Canonical SPipe generation for source `7b37ebfe0181f5a035320880a940927212fbc0e27febdd5093593501597bac91`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b37ebfe0181f5a035320880a940927212fbc0e27febdd5093593501597bac91`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b37ebfe0181f5a035320880a940927212fbc0e27febdd5093593501597bac91`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_complex_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_complex_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_complex_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_complex_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_complex_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats and parses Excel-style complex text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_complex_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes modulus, conjugate, sum, difference, product' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_complex_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TODAY returns a serial consistent with the date pack' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
