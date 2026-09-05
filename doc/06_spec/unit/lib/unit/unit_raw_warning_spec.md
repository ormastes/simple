# Unit Raw Warning Specification

> Tests covering raw_unit lint — raw primitive, raw_unit lint — suffixed literal, raw_unit lint — explicit conversion, raw_unit lint — suppression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Raw Warning Specification

## Scenarios

### raw_unit lint — raw primitive

#### AC-4: `f(10)` where `f(d: km)` emits a `raw_unit` warning

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-4: `f(10)` where `f(d: km)` emits a `raw_unit` warning
   - Expected: expected_code equals `raw_unit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: `f(10)` where `f(d: km)` emits a `raw_unit` warning")
# pending: compiler_diagnostics_for_source(src).codes
val expected_code: text = "raw_unit"
expect(expected_code).to_equal("raw_unit")
```

</details>

#### AC-4: warning message names the parameter and suggests the postfix

- AC-4: warning message names the parameter and suggests the postfix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: warning message names the parameter and suggests the postfix")
val msg: text = "warning: raw primitive passed to unit-typed parameter 'd: km'; use '_km' postfix or explicit conversion"
expect(msg).to_contain("'d: km'")
expect(msg).to_contain("_km")
```

</details>

### raw_unit lint — suffixed literal

#### AC-4: `f(10_km)` emits no `raw_unit` warning

- AC-4: `f(10_km)` emits no `raw_unit` warning
   - Expected: emitted_codes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: `f(10_km)` emits no `raw_unit` warning")
val d = 10_km
val result = travel(d)
# pending: compiler_diagnostics_for_source(src).codes does NOT contain "raw_unit"
val emitted_codes: [text] = []
expect(emitted_codes.len()).to_equal(0)
```

</details>

### raw_unit lint — explicit conversion

#### AC-4: `f(i32_to_km(10))` emits no `raw_unit` warning

- AC-4: `f(i32_to_km(10))` emits no `raw_unit` warning
   - Expected: emitted_codes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: `f(i32_to_km(10))` emits no `raw_unit` warning")
val d = i32_to_km(10)
val result = travel(d)
val emitted_codes: [text] = []
expect(emitted_codes.len()).to_equal(0)
```

</details>

### raw_unit lint — suppression

#### AC-4: a call-site raw-unit suppression silences the warning

- AC-4: a call-site raw-unit suppression silences the warning
   - Expected: suppressed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: a call-site raw-unit suppression silences the warning")
# pending: parse + lint with attribute allow-list; diagnostics stays empty
val suppressed: bool = true
expect(suppressed).to_equal(true)
```

</details>

#### AC-4: an enclosing-function raw-unit suppression silences all call sites

- AC-4: an enclosing-function raw-unit suppression silences all call sites
   - Expected: suppressed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: an enclosing-function raw-unit suppression silences all call sites")
val suppressed: bool = true
expect(suppressed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/unit/unit_raw_warning_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering raw_unit lint — raw primitive, raw_unit lint — suffixed literal, raw_unit lint — explicit conversion, raw_unit lint — suppression.
- raw_unit lint — raw primitive
- raw_unit lint — suffixed literal
- raw_unit lint — explicit conversion
- raw_unit lint — suppression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `da5421d12d1ebcbb51174f26141d0b36008525194649a1af9375764f75c1671e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da5421d12d1ebcbb51174f26141d0b36008525194649a1af9375764f75c1671e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da5421d12d1ebcbb51174f26141d0b36008525194649a1af9375764f75c1671e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/unit/unit_raw_warning_spec.spl
mirror: doc/06_spec/unit/lib/unit/unit_raw_warning_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/unit/unit_raw_warning_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/unit/unit_raw_warning_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/unit/unit_raw_warning_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/unit/unit_raw_warning_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: `f(10)` where `f(d: km)` emits a `raw_unit` warning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/unit/unit_raw_warning_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: warning message names the parameter and suggests the postfix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/unit/unit_raw_warning_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: `f(10_km)` emits no `raw_unit` warning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
