# At Supports Wpt Specification

> Tests covering WPT CSS @supports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# At Supports Wpt Specification

## Scenarios

### WPT CSS @supports

#### @supports conditional rules

#### @supports (display: flex) applies rules

- @supports (display: flex) applies rules


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("@supports (display: flex) applies rules")
expect(_renders_color(
    "@supports (display: flex) { div { width: 12px; height: 8px; background-color: #0891b2; } }",
    "<div></div>",
    0xFF0891B2u32
)).to_equal(true)
```

</details>

#### @supports (display: invalid) rejects known property with invalid value

- @supports (display: invalid) rejects known property with invalid value
   - Expected: not rendered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("@supports (display: invalid) rejects known property with invalid value")
val rendered = _renders_color(
    "@supports (display: definitely-not-css) { div { width: 12px; height: 8px; background-color: #dc2626; } }",
    "<div></div>",
    0xFFDC2626u32
)
expect(not rendered).to_equal(true)
```

</details>

#### @supports (nonexistent: value) does not apply

- @supports (nonexistent: value) does not apply
   - Expected: not rendered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("@supports (nonexistent: value) does not apply")
val rendered = _renders_color(
    "@supports (nonexistent: value) { div { width: 12px; height: 8px; background-color: #dc2626; } }",
    "<div></div>",
    0xFFDC2626u32
)
expect(not rendered).to_equal(true)
```

</details>

#### @supports not (nonexistent: value) applies rules

- @supports not (nonexistent: value) applies rules


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("@supports not (nonexistent: value) applies rules")
expect(_renders_color(
    "@supports not (nonexistent: value) { div { width: 12px; height: 8px; background-color: #16a34a; } }",
    "<div></div>",
    0xFF16A34Au32
)).to_equal(true)
```

</details>

#### @supports (text-overflow: ellipsis) applies text rules

- @supports (text-overflow: ellipsis) applies text rules


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("@supports (text-overflow: ellipsis) applies text rules")
expect(_renders_color(
    "@supports (text-overflow: ellipsis) { div { width: 12px; height: 8px; background-color: #7c3aed; text-overflow: ellipsis; } }",
    "<div></div>",
    0xFF7C3AEDu32
)).to_equal(true)
```

</details>

#### @supports (text-transform: uppercase) applies text rules

- @supports (text-transform: uppercase) applies text rules


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("@supports (text-transform: uppercase) applies text rules")
expect(_renders_color(
    "@supports (text-transform: uppercase) { div { width: 12px; height: 8px; background-color: #be123c; text-transform: uppercase; } }",
    "<div></div>",
    0xFFBE123Cu32
)).to_equal(true)
```

</details>

#### @supports selector(:has()) applies supported selector rules

- @supports selector(:has()) applies supported selector rules


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("@supports selector(:has()) applies supported selector rules")
expect(_renders_color(
    "@supports selector(div:has(.badge)) { div:has(.badge) { width: 12px; height: 8px; background-color: #0e7490; } }",
    "<div><span class='badge'></span></div>",
    0xFF0E7490u32
)).to_equal(true)
```

</details>

#### @supports selector() rejects unsupported pseudo selectors

- @supports selector() rejects unsupported pseudo selectors
   - Expected: not rendered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("@supports selector() rejects unsupported pseudo selectors")
val rendered = _renders_color(
    "@supports selector(div:popover-open) { div { width: 12px; height: 8px; background-color: #dc2626; } }",
    "<div></div>",
    0xFFDC2626u32
)
expect(not rendered).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/at_supports_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WPT CSS @supports.
- WPT CSS @supports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `4ccf4b65dd7a8d65eb70a6c4fb8a7148aeda147db383f3927b27c4e05768a66e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ccf4b65dd7a8d65eb70a6c4fb8a7148aeda147db383f3927b27c4e05768a66e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ccf4b65dd7a8d65eb70a6c4fb8a7148aeda147db383f3927b27c4e05768a66e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/web_platform/css/at_supports_wpt_spec.spl
mirror: doc/06_spec/feature/web_platform/css/at_supports_wpt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/at_supports_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/at_supports_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/at_supports_wpt_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '@supports (display: flex) applies rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/at_supports_wpt_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '@supports (display: invalid) rejects known property with invalid value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/at_supports_wpt_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '@supports (nonexistent: value) does not apply' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
