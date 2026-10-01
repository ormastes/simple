# Tmp Group A Specification

> Tests covering group A - engine2d and fixtures.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Group A Specification

## Scenarios

### group A - engine2d and fixtures

#### Engine2D bridge keeps explicit backend rendering available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Engine2D bridge keeps explicit backend rendering available


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Engine2D bridge keeps explicit backend rendering available")
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val explicit_renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
val explicit_pixels = explicit_renderer.render_html_to_pixels(html).pixel_data
expect(_count_color(explicit_pixels, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### Engine2D GPU bridge requests Metal while preserving CPU parity fallback

- Engine2D GPU bridge requests Metal while preserving CPU parity fallback
   - Expected: gpu_renderer.backend_name() equals `metal`
   - Expected: cpu_renderer.backend_name() equals `cpu`
   - Expected: _pixels_equal(gpu_pixels, cpu_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Engine2D GPU bridge requests Metal while preserving CPU parity fallback")
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val gpu_renderer = create_gpu_browser_renderer(TEST_WIDTH, TEST_HEIGHT)
val cpu_renderer = create_gpu_browser_renderer_with_backend(TEST_WIDTH, TEST_HEIGHT, "cpu")
val gpu_pixels = gpu_renderer.render_html_to_pixels(html).pixel_data
val cpu_pixels = cpu_renderer.render_html_to_pixels(html).pixel_data
expect(gpu_renderer.backend_name()).to_equal("metal")
expect(cpu_renderer.backend_name()).to_equal("cpu")
expect(_count_color(gpu_pixels, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_pixels_equal(gpu_pixels, cpu_pixels)).to_equal(true)
```

</details>

#### renders CSS background fixture

- renders CSS background fixture
   - Expected: pixels.len() equals `40 * 70`
   - Expected: pixels[0] equals `0xFFF0F0F8u32`
   - Expected: pixels[8 + 8 * 40] equals `0xFFD0D8E8u32`
   - Expected: pixels[27 + 61 * 40] equals `0xFFBFDBFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders CSS background fixture")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("15_background"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[0]).to_equal(0xFFF0F0F8u32)
expect(pixels[8 + 8 * 40]).to_equal(0xFFD0D8E8u32)
expect(pixels[27 + 61 * 40]).to_equal(0xFFBFDBFEu32)
```

</details>

#### renders CSS color fixture

- renders CSS color fixture
   - Expected: pixels.len() equals `40 * 70`
   - Expected: pixels[8 + 8 * 40] equals `0xFFDBEAFEu32`
   - Expected: pixels[8 + 28 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[8 + 48 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders CSS color fixture")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("10_colors"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[8 + 8 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[8 + 28 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[8 + 48 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS padding fixture

- renders CSS padding fixture
   - Expected: pixels.len() equals `40 * 90`
   - Expected: pixels[16 + 16 * 40] equals `0xFFDBEAFEu32`
   - Expected: pixels[22 + 50 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[22 + 78 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders CSS padding fixture")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("12_padding"), 40, 90).pixel_data
expect(pixels.len()).to_equal(40 * 90)
expect(pixels[16 + 16 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[22 + 50 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[22 + 78 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS margin fixture

- renders CSS margin fixture
   - Expected: pixels.len() equals `40 * 95`
   - Expected: pixels[14 + 14 * 40] equals `0xFFDBEAFEu32`
   - Expected: pixels[22 + 52 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[22 + 82 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders CSS margin fixture")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("13_margin"), 40, 95).pixel_data
expect(pixels.len()).to_equal(40 * 95)
expect(pixels[14 + 14 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[22 + 52 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[22 + 82 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS border fixture

- renders CSS border fixture
   - Expected: pixels.len() equals `40 * 70`
   - Expected: pixels[4 + 4 * 40] equals `0xFF1A1A1Au32`
   - Expected: pixels[18 + 18 * 40] equals `0xFF003366u32`
   - Expected: pixels[27 + 61 * 40] equals `0xFF006600u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders CSS border fixture")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("14_border"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[4 + 4 * 40]).to_equal(0xFF1A1A1Au32)
expect(pixels[18 + 18 * 40]).to_equal(0xFF003366u32)
expect(pixels[27 + 61 * 40]).to_equal(0xFF006600u32)
```

</details>

#### renders CSS flex row fixture

- renders CSS flex row fixture
   - Expected: pixels.len() equals `125 * 70`
   - Expected: pixels[121 + 61 * 125] equals `0xFF93C5FDu32`
   - Expected: pixels[27 + 61 * 125] equals `0xFFBFDBFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders CSS flex row fixture")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("16_flex_row"), 125, 70).pixel_data
expect(pixels.len()).to_equal(125 * 70)
expect(pixels[121 + 61 * 125]).to_equal(0xFF93C5FDu32)
expect(pixels[27 + 61 * 125]).to_equal(0xFFBFDBFEu32)
```

</details>

#### renders CSS flex col fixture

- renders CSS flex col fixture
   - Expected: pixels.len() equals `40 * 100`
   - Expected: pixels[27 + 61 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[27 + 95 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders CSS flex col fixture")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("17_flex_col"), 40, 100).pixel_data
expect(pixels.len()).to_equal(40 * 100)
expect(pixels[27 + 61 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[27 + 95 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_group_a_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering group A - engine2d and fixtures.
- group A - engine2d and fixtures

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `6373b4654e03609fc0093d93fa8edacc63faca936c5a432c89a95dbe58153202`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6373b4654e03609fc0093d93fa8edacc63faca936c5a432c89a95dbe58153202`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6373b4654e03609fc0093d93fa8edacc63faca936c5a432c89a95dbe58153202`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_group_a_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_group_a_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_group_a_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_group_a_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_group_a_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Engine2D bridge keeps explicit backend rendering available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_group_a_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Engine2D GPU bridge requests Metal while preserving CPU parity fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_group_a_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders CSS background fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
