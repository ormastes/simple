# math_editor_spec

> LibreOffice Math — equation editor spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math_editor_spec

LibreOffice Math — equation editor spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/math_editor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

LibreOffice Math — equation editor spec.

Verifies the Math component: a simple math expression renders to MathML
(identifiers→<mi>, numbers→<mn>, operators→<mo>), with structured superscript
and square-root helpers. The renderer is the display core of an equation editor.

## Scenarios

### Math editor: flat expression to MathML

#### wraps output in a MathML math/mrow root

- wraps output in a MathML math/mrow root


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps output in a MathML math/mrow root")
val ml = math_to_mathml("a + 1")
expect(ml).to_start_with("<math ")
expect(ml).to_contain("<mrow>")
expect(ml).to_end_with("</math>")
```

</details>

#### renders an identifier as <mi>

- renders an identifier as <mi>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an identifier as <mi>")
val ml = math_to_mathml("a + 1")
expect(ml).to_contain("<mi>a</mi>")
```

</details>

#### renders a multi-digit number as <mn>

- renders a multi-digit number as <mn>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a multi-digit number as <mn>")
val ml = math_to_mathml("x + 12")
expect(ml).to_contain("<mn>12</mn>")
```

</details>

#### renders an operator as <mo>

- renders an operator as <mo>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an operator as <mo>")
val ml = math_to_mathml("a + b")
expect(ml).to_contain("<mo>+</mo>")
```

</details>

### Math editor: structured forms
_Superscript and square root produce structured MathML._

#### renders a superscript with msup

- renders a superscript with msup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a superscript with msup")
val ml = math_superscript("x", "2")
expect(ml).to_start_with("<msup>")
expect(ml).to_contain("<mi>x</mi>")
expect(ml).to_contain("<mn>2</mn>")
```

</details>

#### renders a square root with msqrt

- renders a square root with msqrt


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a square root with msqrt")
val ml = math_sqrt("y")
expect(ml).to_start_with("<msqrt>")
expect(ml).to_contain("<mi>y</mi>")
```

</details>

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

- Canonical SPipe generation for source `cb9b2c9fdc4013f6daa97957141d9148bb9c946f0825bc5ce04e5331d3f367ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb9b2c9fdc4013f6daa97957141d9148bb9c946f0825bc5ce04e5331d3f367ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb9b2c9fdc4013f6daa97957141d9148bb9c946f0825bc5ce04e5331d3f367ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/math_editor_spec.spl
mirror: doc/06_spec/01_unit/app/office/math_editor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/math_editor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/math_editor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/math_editor_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps output in a MathML math/mrow root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/math_editor_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders an identifier as <mi>' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/math_editor_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a multi-digit number as <mn>' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
