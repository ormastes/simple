# Ios Css Specification

> Tests covering ios_css, ios_css_overrides.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ios Css Specification

## Scenarios

### ios_css

### ios_css_overrides

#### AC-5: returns a non-empty CSS string

- AC-5: returns a non-empty CSS string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: returns a non-empty CSS string")
val css = ios_css_overrides()
expect(css.len()).to_be_greater_than(0)
```

</details>

#### AC-5: contains -webkit-overflow-scrolling for touch scroll

- AC-5: contains -webkit-overflow-scrolling for touch scroll


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: contains -webkit-overflow-scrolling for touch scroll")
val css = ios_css_overrides()
expect(css).to_contain("-webkit-overflow-scrolling")
```

</details>

#### AC-5: contains iOS accent color #007AFF

- AC-5: contains iOS accent color #007AFF


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: contains iOS accent color #007AFF")
val css = ios_css_overrides()
expect(css).to_contain("#007AFF")
```

</details>

#### AC-5: contains 44px touch target min-height

- AC-5: contains 44px touch target min-height


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: contains 44px touch target min-height")
val css = ios_css_overrides()
expect(css).to_contain("min-height: 44px")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/ios_css_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ios_css, ios_css_overrides.
- ios_css
- ios_css_overrides

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

- Canonical SPipe generation for source `91397859a75b5ca5100c0a971883698bcd66f8cf01812e14be7ef48cb82807b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `91397859a75b5ca5100c0a971883698bcd66f8cf01812e14be7ef48cb82807b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `91397859a75b5ca5100c0a971883698bcd66f8cf01812e14be7ef48cb82807b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/llm_dashboard/ios_css_spec.spl
mirror: doc/06_spec/unit/app/llm_dashboard/ios_css_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_dashboard/ios_css_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_dashboard/ios_css_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_dashboard/ios_css_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: returns a non-empty CSS string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/ios_css_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: contains -webkit-overflow-scrolling for touch scroll' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/ios_css_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: contains iOS accent color #007AFF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
