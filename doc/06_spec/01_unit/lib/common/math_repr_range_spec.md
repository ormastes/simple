# Math Repr Range Specification

> Tests covering math_repr range handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Repr Range Specification

## Scenarios

### math_repr range handling

#### bounded operators split the range into sub/superscript

#### renders sum bounds as _{var=from}^{to}

- renders sum bounds as _{var=from}^{to}
   - Expected: render_latex_raw("sum(i, 1..n) i") equals `\\sum_\{i=1\}^\{n\} i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders sum bounds as _{var=from}^{to}")
expect(render_latex_raw("sum(i, 1..n) i")).to_equal("\\sum_\{i=1\}^\{n\} i")
```

</details>

#### renders int bounds as _{from}^{to}

- renders int bounds as _{from}^{to}
   - Expected: render_latex_raw("int(x, 0..1) x") equals `\\int_\{0\}^\{1\} x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders int bounds as _{from}^{to}")
expect(render_latex_raw("int(x, 0..1) x")).to_equal("\\int_\{0\}^\{1\} x")
```

</details>

#### the range production keeps both bounds everywhere else

#### renders a bare range

- renders a bare range
   - Expected: render_latex_raw("1..n") equals `1 \\ldots n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a bare range")
expect(render_latex_raw("1..n")).to_equal("1 \\ldots n")
```

</details>

#### renders a range inside a known-function argument list

- renders a range inside a known-function argument list
   - Expected: render_latex_raw("lim(x, 0..1) x") equals `\\lim(x, 0 \\ldots 1) x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a range inside a known-function argument list")
expect(render_latex_raw("lim(x, 0..1) x")).to_equal("\\lim(x, 0 \\ldots 1) x")
```

</details>

#### renders a range inside a plain function-call argument

- renders a range inside a plain function-call argument
   - Expected: render_latex_raw("f(1..n)") equals `\\operatorname\{f\}(1 \\ldots n)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a range inside a plain function-call argument")
expect(render_latex_raw("f(1..n)")).to_equal("\\operatorname\{f\}(1 \\ldots n)")
```

</details>

#### renders a range inside a subscript bracket

- renders a range inside a subscript bracket
   - Expected: render_latex_raw("a[1..n]") equals `a_\{1 \\ldots n\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a range inside a subscript bracket")
expect(render_latex_raw("a[1..n]")).to_equal("a_\{1 \\ldots n\}")
```

</details>

#### range splitting is nesting-aware

#### splits int bounds on the top-level .. not a nested one

- splits int bounds on the top-level .. not a nested one
   - Expected: render_latex_raw("int(x, f(a..b)..n) x") equals `\\int_\{\\operatorname\{f\}(a \\ldots b)\}^\{n\} x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits int bounds on the top-level .. not a nested one")
expect(render_latex_raw("int(x, f(a..b)..n) x")).to_equal("\\int_\{\\operatorname\{f\}(a \\ldots b)\}^\{n\} x")
```

</details>

#### the other renderers keep both bounds too

#### pretty keeps the range

- pretty keeps the range
   - Expected: to_pretty("f(1..n)") equals `f(1..n)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pretty keeps the range")
expect(to_pretty("f(1..n)")).to_equal("f(1..n)")
```

</details>

#### text keeps the range

- text keeps the range
   - Expected: to_text("f(1..n)") equals `f(1..n)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text keeps the range")
expect(to_text("f(1..n)")).to_equal("f(1..n)")
```

</details>

#### debug emits a Range node

- debug emits a Range node
   - Expected: to_debug("f(1..n)") equals `Call(f, Range(Num(1), Id(n)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug emits a Range node")
expect(to_debug("f(1..n)")).to_equal("Call(f, Range(Num(1), Id(n)))")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math_repr_range_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering math_repr range handling.
- math_repr range handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `63b02140429bd58fb379d8bf429d7c0ca62ba8a465263905342e41c984176712`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63b02140429bd58fb379d8bf429d7c0ca62ba8a465263905342e41c984176712`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63b02140429bd58fb379d8bf429d7c0ca62ba8a465263905342e41c984176712`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math_repr_range_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math_repr_range_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math_repr_range_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math_repr_range_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math_repr_range_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders sum bounds as _{var=from}^{to}' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_range_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders int bounds as _{from}^{to}' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_range_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a bare range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
