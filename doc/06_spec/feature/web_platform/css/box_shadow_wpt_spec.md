# Box Shadow Wpt Specification

> Tests covering WPT-derived box-shadow fallback rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Box Shadow Wpt Specification

## Scenarios

### WPT-derived box-shadow fallback rendering

#### renders single-layer offset box shadow behind the block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders single-layer offset box shadow behind the block
   - Expected: _pixel_at(pixels, 10, 4) equals `0xFF16A34Au32`
   - Expected: _pixel_at(pixels, 2, 2) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders single-layer offset box shadow behind the block")
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 4px 3px 0 #16a34a; }", "<div></div>")
expect(_pixel_at(pixels, 10, 4)).to_equal(0xFF16A34Au32)
expect(_pixel_at(pixels, 2, 2)).to_equal(0xFFFFFFFFu32)
```

</details>

#### renders blur-radius shadow coverage

- renders blur-radius shadow coverage
   - Expected: _pixel_at(pixels, 9, 1) equals `0xFFDC2626u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders blur-radius shadow coverage")
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 2px #dc2626; }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFFDC2626u32)
```

</details>

#### parses blur and spread lengths before the shadow color

- parses blur and spread lengths before the shadow color
   - Expected: _pixel_at(pixels, 9, 1) equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses blur and spread lengths before the shadow color")
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 0px 2px #2563eb; }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFF2563EBu32)
```

</details>

#### keeps functional rgb shadow colors intact while tokenizing

- keeps functional rgb shadow colors intact while tokenizing
   - Expected: _pixel_at(pixels, 9, 1) equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps functional rgb shadow colors intact while tokenizing")
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 0px 2px rgb(37, 99, 235); }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFF2563EBu32)
```

</details>

#### composites functional rgba shadow colors over the white page

- composites functional rgba shadow colors over the white page
   - Expected: _pixel_at(pixels, 9, 1) equals `0xFF92B1F5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("composites functional rgba shadow colors over the white page")
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 0px 2px rgba(37, 99, 235, 0.5); }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFF92B1F5u32)
```

</details>

#### resolves named shadow colors through the shared color table

- resolves named shadow colors through the shared color table
   - Expected: _pixel_at(pixels, 9, 1) equals `0xFF663399u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves named shadow colors through the shared color table")
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 0px 2px rebeccapurple; }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFF663399u32)
```

</details>

#### keeps functional hsl shadow colors intact while tokenizing

- keeps functional hsl shadow colors intact while tokenizing
   - Expected: _pixel_at(pixels, 9, 1) equals `0xFF00FF00u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps functional hsl shadow colors intact while tokenizing")
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 0px 0px 0px 2px hsl(120, 100%, 50%); }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFF00FF00u32)
```

</details>

#### resolves currentColor shadow colors from the element style

- resolves currentColor shadow colors from the element style
   - Expected: _pixel_at(pixels, 9, 1) equals `0xFFDB2777u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves currentColor shadow colors from the element style")
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; color: #db2777; box-shadow: 0px 0px 0px 2px currentColor; }", "<div></div>")
expect(_pixel_at(pixels, 9, 1)).to_equal(0xFFDB2777u32)
```

</details>

#### renders comma-separated non-inset box shadow layers

- renders comma-separated non-inset box shadow layers
   - Expected: _pixel_at(pixels, 10, 1) equals `0xFFDC2626u32`
   - Expected: _pixel_at(pixels, 1, 8) equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders comma-separated non-inset box shadow layers")
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: 4px 0px 0px #dc2626, 0px 4px 0px #2563eb; }", "<div></div>")
expect(_pixel_at(pixels, 10, 1)).to_equal(0xFFDC2626u32)
expect(_pixel_at(pixels, 1, 8)).to_equal(0xFF2563EBu32)
```

</details>

#### renders simple inset box shadows before text painting

- renders simple inset box shadows before text painting
   - Expected: _pixel_at(pixels, 1, 0) equals `0xFF16A34Au32`
   - Expected: _pixel_at(pixels, 4, 3) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renders simple inset box shadows before text painting")
val pixels = _render("div { width: 8px; height: 6px; background-color: #ffffff; box-shadow: inset 0px 0px 0px 2px #16a34a; }", "<div></div>")
expect(_pixel_at(pixels, 1, 0)).to_equal(0xFF16A34Au32)
expect(_pixel_at(pixels, 4, 3)).to_equal(0xFFFFFFFFu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/box_shadow_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WPT-derived box-shadow fallback rendering.
- WPT-derived box-shadow fallback rendering

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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9de8fa73e8b032e6f95bef61bb63038e247560308193c1720d51bf5617dd4844`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9de8fa73e8b032e6f95bef61bb63038e247560308193c1720d51bf5617dd4844`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9de8fa73e8b032e6f95bef61bb63038e247560308193c1720d51bf5617dd4844`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/web_platform/css/box_shadow_wpt_spec.spl
mirror: doc/06_spec/feature/web_platform/css/box_shadow_wpt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/box_shadow_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/box_shadow_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/box_shadow_wpt_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders single-layer offset box shadow behind the block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/box_shadow_wpt_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders blur-radius shadow coverage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/box_shadow_wpt_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses blur and spread lengths before the shadow color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
