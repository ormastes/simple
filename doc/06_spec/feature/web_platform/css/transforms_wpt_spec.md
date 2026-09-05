# Transforms Wpt Specification

> Tests covering WPT-derived CSS transforms subset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transforms Wpt Specification

## Scenarios

### WPT-derived CSS transforms subset

#### CSS transform property

#### translate moves element

- translate moves element
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 4, 4) equals `0xFFDC2626u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("translate moves element")
val pixels = _render(
    "div { width: 4px; height: 4px; background-color: #dc2626; transform: translate(4px, 4px); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 4, 4)).to_equal(0xFFDC2626u32)
```

</details>

#### translateX moves element on the inline axis

- translateX moves element on the inline axis
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 5, 0) equals `0xFF16A34Au32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("translateX moves element on the inline axis")
val pixels = _render(
    "div { width: 4px; height: 4px; background-color: #16a34a; transform: translateX(5px); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 5, 0)).to_equal(0xFF16A34Au32)
```

</details>

#### translateY moves element on the block axis

- translateY moves element on the block axis
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 0, 5) equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("translateY moves element on the block axis")
val pixels = _render(
    "div { width: 4px; height: 4px; background-color: #2563eb; transform: translateY(5px); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 0, 5)).to_equal(0xFF2563EBu32)
```

</details>

#### percentage translate uses element dimensions

- percentage translate uses element dimensions
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 5, 2) equals `0xFFEA580Cu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("percentage translate uses element dimensions")
val pixels = _render(
    "div { width: 10px; height: 8px; background-color: #ea580c; transform: translate(50%, 25%); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 5, 2)).to_equal(0xFFEA580Cu32)
```

</details>

#### space-separated percentage translate uses element dimensions

- space-separated percentage translate uses element dimensions
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 5, 2) equals `0xFF0F766Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("space-separated percentage translate uses element dimensions")
val pixels = _render(
    "div { width: 10px; height: 8px; background-color: #0f766e; transform: translate(50% 25%); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 5, 2)).to_equal(0xFF0F766Eu32)
```

</details>

#### percentage translateX uses element width

- percentage translateX uses element width
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 5, 0) equals `0xFF7C3AEDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("percentage translateX uses element width")
val pixels = _render(
    "div { width: 10px; height: 4px; background-color: #7c3aed; transform: translateX(50%); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 5, 0)).to_equal(0xFF7C3AEDu32)
```

</details>

#### percentage translateY uses element height

- percentage translateY uses element height
   - Expected: _pixel_at(pixels, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 0, 2) equals `0xFF0891B2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("percentage translateY uses element height")
val pixels = _render(
    "div { width: 4px; height: 8px; background-color: #0891b2; transform: translateY(25%); }",
    "<div></div>")
expect(_pixel_at(pixels, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 0, 2)).to_equal(0xFF0891B2u32)
```

</details>

#### scale(2) keeps transformed color visible

- scale(2) keeps transformed color visible
   - Expected: no_scale > 0 is true
   - Expected: with_scale >= no_scale is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("scale(2) keeps transformed color visible")
val no_scale = _pixel_count(
    "div { width: 6px; height: 4px; background-color: #16a34a; }",
    "<div></div>",
    0xFF16A34Au32)
val with_scale = _pixel_count(
    "div { width: 6px; height: 4px; background-color: #16a34a; transform: scale(2); }",
    "<div></div>",
    0xFF16A34Au32)
expect(no_scale > 0).to_equal(true)
expect(with_scale >= no_scale).to_equal(true)
```

</details>

#### rotate(0deg) keeps transformed color visible

- rotate(0deg) keeps transformed color visible
   - Expected: no_rotate > 0 is true
   - Expected: with_rotate > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rotate(0deg) keeps transformed color visible")
val no_rotate = _pixel_count(
    "div { width: 12px; height: 8px; background-color: #7c3aed; }",
    "<div></div>",
    0xFF7C3AEDu32)
val with_rotate = _pixel_count(
    "div { width: 12px; height: 8px; background-color: #7c3aed; transform: rotate(0deg); }",
    "<div></div>",
    0xFF7C3AEDu32)
expect(no_rotate > 0).to_equal(true)
expect(with_rotate > 0).to_equal(true)
```

</details>

#### transform-origin keeps rotated color visible

- transform-origin keeps rotated color visible
   - Expected: center_origin is true
   - Expected: corner_origin is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transform-origin keeps rotated color visible")
val center_origin = _renders_color(
    "div { width: 8px; height: 8px; background-color: #0891b2; transform: rotate(45deg); transform-origin: 50% 50%; }",
    "<div></div>",
    0xFF0891B2u32)
val corner_origin = _renders_color(
    "div { width: 8px; height: 8px; background-color: #0891b2; transform: rotate(45deg); transform-origin: 0% 0%; }",
    "<div></div>",
    0xFF0891B2u32)
expect(center_origin).to_equal(true)
expect(corner_origin).to_equal(true)
```

</details>

#### multiple transforms keep composed color visible

- multiple transforms keep composed color visible
   - Expected: composed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple transforms keep composed color visible")
val composed = _renders_color(
    "div { width: 8px; height: 6px; background-color: #ea580c; transform: translate(2px, 0px) scale(1.5); }",
    "<div></div>",
    0xFFEA580Cu32)
expect(composed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/transforms_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WPT-derived CSS transforms subset.
- WPT-derived CSS transforms subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `3bcd8ae5f936594252cf5996705f834c3f6dc19d6ce54d018a47588737104a3f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3bcd8ae5f936594252cf5996705f834c3f6dc19d6ce54d018a47588737104a3f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3bcd8ae5f936594252cf5996705f834c3f6dc19d6ce54d018a47588737104a3f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/web_platform/css/transforms_wpt_spec.spl
mirror: doc/06_spec/feature/web_platform/css/transforms_wpt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/transforms_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/transforms_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/transforms_wpt_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translate moves element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/transforms_wpt_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translateX moves element on the inline axis' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/transforms_wpt_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translateY moves element on the block axis' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
