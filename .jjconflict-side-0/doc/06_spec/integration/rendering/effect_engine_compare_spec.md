# Effect Engine Compare Specification

> Tests covering Effect Engine Comparison (Int32 vs Float64).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effect Engine Compare Specification

## Scenarios

### Effect Engine Comparison (Int32 vs Float64)

#### full scene comparison

#### glass_dark renders within effect engine tolerance

- glass_dark renders within effect engine tolerance
   - Expected: int_cap.success is true
   - Expected: float_cap.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("glass_dark renders within effect engine tolerance")
val html = generate_glass_test_html("glass_dark")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
val result = compare_pixel_buffers(int_cap.pixels, float_cap.pixels, W, H, THRESHOLD_EE)
expect(result.match_percentage).to_be_greater_than(MIN_PCT_EE - 1)
if result.match_percentage < 10000:
    print "Int32 vs Float64 on glass_dark:"
    print_comparison_report(result)
```

</details>

#### glass_light renders within effect engine tolerance

- glass_light renders within effect engine tolerance
   - Expected: int_cap.success is true
   - Expected: float_cap.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("glass_light renders within effect engine tolerance")
val html = generate_glass_test_html("glass_light")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
val result = compare_pixel_buffers(int_cap.pixels, float_cap.pixels, W, H, THRESHOLD_EE)
expect(result.match_percentage).to_be_greater_than(MIN_PCT_EE - 1)
```

</details>

<details>
<summary>Advanced: stress test renders within effect engine tolerance</summary>

#### stress test renders within effect engine tolerance

- stress test renders within effect engine tolerance
   - Expected: int_cap.success is true
   - Expected: float_cap.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stress test renders within effect engine tolerance")
val html = build_rendering_stress_html()
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
val result = compare_pixel_buffers(int_cap.pixels, float_cap.pixels, W, H, THRESHOLD_EE)
expect(result.match_percentage).to_be_greater_than(MIN_PCT_EE - 1)
```

</details>


</details>

#### per-channel analysis

#### glass_dark per-channel diff within tolerance

- glass_dark per-channel diff within tolerance
   - Expected: int_cap.success is true
   - Expected: float_cap.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("glass_dark per-channel diff within tolerance")
val html = generate_glass_test_html("glass_dark")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
val channels = compare_per_channel(int_cap.pixels, float_cap.pixels, W, H, THRESHOLD_EE)
print_channel_report(channels)
# Each channel should be within tolerance
for ch in channels:
    expect(ch.match_pct).to_be_greater_than(MIN_PCT_EE - 1)
```

</details>

#### pixel buffer sizes match

#### int and float engines produce same buffer size

- int and float engines produce same buffer size
   - Expected: int_cap.success is true
   - Expected: float_cap.success is true
   - Expected: int_cap.pixels.len() equals `float_cap.pixels.len()`
   - Expected: int_cap.pixels.len() equals `W * H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("int and float engines produce same buffer size")
val html = generate_glass_test_html("glass_dark")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
expect(int_cap.pixels.len()).to_equal(float_cap.pixels.len())
expect(int_cap.pixels.len()).to_equal(W * H)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/effect_engine_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Effect Engine Comparison (Int32 vs Float64).
- Effect Engine Comparison (Int32 vs Float64)

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c6ca63245ff1afd701524fa155ca21a2a29da7eaaa7269596a567c5468fa394f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c6ca63245ff1afd701524fa155ca21a2a29da7eaaa7269596a567c5468fa394f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c6ca63245ff1afd701524fa155ca21a2a29da7eaaa7269596a567c5468fa394f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/integration/rendering/effect_engine_compare_spec.spl
mirror: doc/06_spec/integration/rendering/effect_engine_compare_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/effect_engine_compare_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/integration/rendering/effect_engine_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/effect_engine_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
