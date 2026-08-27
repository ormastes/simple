# Backend Screenshot Compare Specification

> Tests covering Backend Screenshot Comparison.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Screenshot Compare Specification

## Scenarios

### Backend Screenshot Comparison

#### Software vs CPU (deterministic)

#### renders glass_dark test page identically

- renders glass_dark test page identically
   - Expected: sw.success is true
   - Expected: cpu.success is true
   - Expected: result.match_percentage equals `MIN_IDENTICAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders glass_dark test page identically")
val html = generate_glass_test_html("glass_dark")
val sw = capture_with_backend(html, W, H, "software")
val cpu = capture_with_backend(html, W, H, "cpu")
expect(sw.success).to_equal(true)
expect(cpu.success).to_equal(true)
val result = compare_exact(sw.pixels, cpu.pixels, W, H)
expect(result.match_percentage).to_equal(MIN_IDENTICAL)
```

</details>

#### renders glass_light test page identically

- renders glass_light test page identically
   - Expected: sw.success is true
   - Expected: cpu.success is true
   - Expected: result.match_percentage equals `MIN_IDENTICAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders glass_light test page identically")
val html = generate_glass_test_html("glass_light")
val sw = capture_with_backend(html, W, H, "software")
val cpu = capture_with_backend(html, W, H, "cpu")
expect(sw.success).to_equal(true)
expect(cpu.success).to_equal(true)
val result = compare_exact(sw.pixels, cpu.pixels, W, H)
expect(result.match_percentage).to_equal(MIN_IDENTICAL)
```

</details>

<details>
<summary>Advanced: renders stress test page identically</summary>

#### renders stress test page identically

- renders stress test page identically
   - Expected: sw.success is true
   - Expected: cpu.success is true
   - Expected: result.match_percentage equals `MIN_IDENTICAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders stress test page identically")
val html = build_rendering_stress_html()
val sw = capture_with_backend(html, W, H, "software")
val cpu = capture_with_backend(html, W, H, "cpu")
expect(sw.success).to_equal(true)
expect(cpu.success).to_equal(true)
val result = compare_exact(sw.pixels, cpu.pixels, W, H)
expect(result.match_percentage).to_equal(MIN_IDENTICAL)
```

</details>


</details>

#### Software vs CUDA

#### renders glass_dark within GPU tolerance

- renders glass_dark within GPU tolerance
   - Expected: sw.success is true
   - Expected: cuda.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders glass_dark within GPU tolerance")
val backends = Engine2D.list_backends()
var has_cuda = false
for b in backends:
    if b == "cuda":
        has_cuda = true
if not has_cuda:
    return
val html = generate_glass_test_html("glass_dark")
val sw = capture_with_backend(html, W, H, "software")
val cuda = capture_with_backend(html, W, H, "cuda")
expect(sw.success).to_equal(true)
expect(cuda.success).to_equal(true)
val result = compare_pixel_buffers(sw.pixels, cuda.pixels, W, H, THRESHOLD_GPU)
expect(result.match_percentage).to_be_greater_than(MIN_GPU - 1)
```

</details>

<details>
<summary>Advanced: renders stress test within GPU tolerance</summary>

#### renders stress test within GPU tolerance

- renders stress test within GPU tolerance
   - Expected: sw.success is true
   - Expected: cuda.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders stress test within GPU tolerance")
val backends = Engine2D.list_backends()
var has_cuda = false
for b in backends:
    if b == "cuda":
        has_cuda = true
if not has_cuda:
    return
val html = build_rendering_stress_html()
val sw = capture_with_backend(html, W, H, "software")
val cuda = capture_with_backend(html, W, H, "cuda")
expect(sw.success).to_equal(true)
expect(cuda.success).to_equal(true)
val result = compare_pixel_buffers(sw.pixels, cuda.pixels, W, H, THRESHOLD_GPU)
expect(result.match_percentage).to_be_greater_than(MIN_GPU - 1)
```

</details>


</details>

#### All available backends

#### all backends agree on glass_dark within GPU tolerance

- all backends agree on glass_dark within GPU tolerance
   - Expected: passed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("all backends agree on glass_dark within GPU tolerance")
val html = generate_glass_test_html("glass_dark")
val captures = capture_all_available(html, W, H)
# Software is always present as baseline
var baseline: BackendCapture? = nil
for cap in captures:
    if cap.backend_name == "software":
        baseline = cap
if val Some(base) = baseline:
    var entries: [BackendCompareEntry] = []
    for cap in captures:
        if cap.backend_name != "software" and cap.success:
            val result = compare_pixel_buffers(base.pixels, cap.pixels, W, H, THRESHOLD_GPU)
            val passed = result.match_percentage >= MIN_GPU
            entries = entries + [BackendCompareEntry(
                backend_name: cap.backend_name,
                result: result,
                threshold: THRESHOLD_GPU,
                passed: passed
            )]
            expect(passed).to_equal(true)
    print_multi_backend_report("glass_dark", "software", entries)
```

</details>

#### Diff image generation

#### produces all-green for identical buffers

- produces all-green for identical buffers
   - Expected: diff.len() equals `size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces all-green for identical buffers")
val size = 10 * 10
var buf_a: [u32] = [0xFF336699u32; size]
var buf_b: [u32] = [0xFF336699u32; size]
val diff = generate_diff_image(buf_a, buf_b, 10, 10)
expect(diff.len()).to_equal(size)
# All pixels should have green > red (green tint for match)
val first = diff[0]
val green = ((first >> 8) & 0xFF).to_i32()
val red = ((first >> 16) & 0xFF).to_i32()
expect(green).to_be_greater_than(red)
```

</details>

#### produces red pixels for differing regions

- produces red pixels for differing regions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces red pixels for differing regions")
var buf_a: [u32] = [0xFF000000u32; 100]
var buf_b: [u32] = [0xFFFFFFFFu32; 100]
val diff = generate_diff_image(buf_a, buf_b, 10, 10)
# All pixels should be red (max difference)
val first = diff[0]
val red = ((first >> 16) & 0xFF).to_i32()
expect(red).to_be_greater_than(100)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/backend_screenshot_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Backend Screenshot Comparison.
- Backend Screenshot Comparison

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `75699df3defda527530d0f35f4410e67a559cd5d2bc5c7d52c0b0d7e575529bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75699df3defda527530d0f35f4410e67a559cd5d2bc5c7d52c0b0d7e575529bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75699df3defda527530d0f35f4410e67a559cd5d2bc5c7d52c0b0d7e575529bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/integration/rendering/backend_screenshot_compare_spec.spl
mirror: doc/06_spec/integration/rendering/backend_screenshot_compare_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=65 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/backend_screenshot_compare_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/integration/rendering/backend_screenshot_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/backend_screenshot_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/backend_screenshot_compare_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces all-green for identical buffers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/backend_screenshot_compare_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces red pixels for differing regions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
