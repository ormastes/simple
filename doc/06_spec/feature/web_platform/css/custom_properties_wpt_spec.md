# Custom Properties Wpt Specification

> Tests covering WPT CSS custom properties.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Properties Wpt Specification

## Scenarios

### WPT CSS custom properties

#### var() resolution

#### var() resolves custom property value

- var() resolves custom property value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("var() resolves custom property value")
expect(_renders_color(
    "div { --color: #dc2626; background-color: var(--color); width: 12px; height: 8px; }",
    "<div></div>",
    0xFFDC2626u32
)).to_equal(true)
```

</details>

#### var() with fallback when undefined

- var() with fallback when undefined


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("var() with fallback when undefined")
expect(_renders_color(
    "div { background-color: var(--undefined, #16a34a); width: 12px; height: 8px; }",
    "<div></div>",
    0xFF16A34Au32
)).to_equal(true)
```

</details>

#### custom property inherits to child

- custom property inherits to child


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("custom property inherits to child")
expect(_renders_color(
    ".parent { --color: #2563eb; } .child { background-color: var(--color); width: 12px; height: 8px; }",
    "<div class='parent'><div class='child'></div></div>",
    0xFF2563EBu32
)).to_equal(true)
```

</details>

#### var() nested fallback

- var() nested fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("var() nested fallback")
expect(_renders_color(
    "div { background-color: var(--a, var(--b, #9333ea)); width: 12px; height: 8px; }",
    "<div></div>",
    0xFF9333EAu32
)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/custom_properties_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WPT CSS custom properties.
- WPT CSS custom properties

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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c73e27fe95248794c7fb7030efa4e2d1fc4bd60434de5a46194409155ca3e0bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c73e27fe95248794c7fb7030efa4e2d1fc4bd60434de5a46194409155ca3e0bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c73e27fe95248794c7fb7030efa4e2d1fc4bd60434de5a46194409155ca3e0bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/web_platform/css/custom_properties_wpt_spec.spl
mirror: doc/06_spec/feature/web_platform/css/custom_properties_wpt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/custom_properties_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/custom_properties_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/custom_properties_wpt_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'var() resolves custom property value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/custom_properties_wpt_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'var() with fallback when undefined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/custom_properties_wpt_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'custom property inherits to child' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
