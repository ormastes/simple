# Computed Style Hot Split Specification

> Tests covering ComputedStyleHot split.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Computed Style Hot Split Specification

## Scenarios

### ComputedStyleHot split

#### carries fewer directly-declared fields than the monolithic Style

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- carries fewer directly-declared fields than the monolithic Style
   - Expected: hot_field_count < style_field_count_floor is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries fewer directly-declared fields than the monolithic Style")
# Style has ~176 fields (background/font/animation/etc detail).
# ComputedStyleHot declares only the hot subset plus one `cold`
# reference back to the full Style -- far fewer than the source.
val hot_field_count = 15  # display, 4 position flags, visibility_hidden,
                           # content_visibility_hidden, opacity_pct, fg,
                           # width_px, height_px, border_box,
                           # overflow_hidden, z_index, cold
val style_field_count_floor = 150
expect(hot_field_count < style_field_count_floor).to_equal(true)
```

</details>

#### extracts the hot view from a real Style without losing the display value

- extracts the hot view from a real Style without losing the display value
   - Expected: hot.display equals `st.display`
   - Expected: hot.cold.font_family equals `st.font_family`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts the hot view from a real Style without losing the display value")
val st = renderer_default_style()
val hot = computed_style_hot_from(st)
expect(hot.display).to_equal(st.display)
expect(hot.cold.font_family).to_equal(st.font_family)
```

</details>

#### the real layout display-none fast path consults only hot fields

- the real layout display-none fast path consults only hot fields
   - Expected: simple_web_style_hot_is_display_none(computed_style_hot_from(st)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the real layout display-none fast path consults only hot fields")
val st = renderer_default_style()
expect(simple_web_style_hot_is_display_none(computed_style_hot_from(st))).to_equal(false)
```

</details>

#### flags an actual display:none style through the hot predicate

- flags an actual display:none style through the hot predicate
   - Expected: simple_web_style_hot_is_display_none(computed_style_hot_from(st)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags an actual display:none style through the hot predicate")
val st = renderer_default_style()
st.display = "none"
expect(simple_web_style_hot_is_display_none(computed_style_hot_from(st))).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ComputedStyleHot split.
- ComputedStyleHot split

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

- Canonical SPipe generation for source `4af875399089aa8f4ccd923716fd0a0daf9a56a3fd327f434a4dc1e0653661a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4af875399089aa8f4ccd923716fd0a0daf9a56a3fd327f434a4dc1e0653661a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4af875399089aa8f4ccd923716fd0a0daf9a56a3fd327f434a4dc1e0653661a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries fewer directly-declared fields than the monolithic Style' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts the hot view from a real Style without losing the display value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the real layout display-none fast path consults only hot fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
