# Dashboard Glass Css Specification

> Tests covering dashboard_glass_css, generate_dashboard_glass_css.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dashboard Glass Css Specification

## Scenarios

### dashboard_glass_css

### generate_dashboard_glass_css

#### AC-1: returns a non-empty CSS string

- AC-1: returns a non-empty CSS string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns a non-empty CSS string")
val css = generate_dashboard_glass_css()
expect(css.len()).to_be_greater_than(0)
```

</details>

#### AC-1: contains Stitch obsidian accent color #0A84FF

- AC-1: contains Stitch obsidian accent color #0A84FF


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: contains Stitch obsidian accent color #0A84FF")
val css = generate_dashboard_glass_css()
expect(css).to_contain("#0A84FF")
```

</details>

#### AC-1: contains backdrop-filter for glass effect

- AC-1: contains backdrop-filter for glass effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: contains backdrop-filter for glass effect")
val css = generate_dashboard_glass_css()
expect(css).to_contain("backdrop-filter")
```

</details>

#### AC-2: contains .tab-btn class binding

- AC-2: contains .tab-btn class binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: contains .tab-btn class binding")
val css = generate_dashboard_glass_css()
expect(css).to_contain(".tab-btn")
```

</details>

#### AC-2: contains body background using Stitch surface token

- AC-2: contains body background using Stitch surface token


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: contains body background using Stitch surface token")
val css = generate_dashboard_glass_css()
expect(css).to_contain("--surface")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/dashboard_glass_css_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering dashboard_glass_css, generate_dashboard_glass_css.
- dashboard_glass_css
- generate_dashboard_glass_css

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

- Canonical SPipe generation for source `3e1022081b59db547d96d046a29bb35e7c03282ea6d5a84a3d48eba0c8f3cc65`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e1022081b59db547d96d046a29bb35e7c03282ea6d5a84a3d48eba0c8f3cc65`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e1022081b59db547d96d046a29bb35e7c03282ea6d5a84a3d48eba0c8f3cc65`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/llm_dashboard/dashboard_glass_css_spec.spl
mirror: doc/06_spec/unit/app/llm_dashboard/dashboard_glass_css_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_dashboard/dashboard_glass_css_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_dashboard/dashboard_glass_css_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_dashboard/dashboard_glass_css_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns a non-empty CSS string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/dashboard_glass_css_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: contains Stitch obsidian accent color #0A84FF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/dashboard_glass_css_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: contains backdrop-filter for glass effect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
