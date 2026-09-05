# Glass Pipeline Screenshot Specification

> Tests covering Glass Pipeline Screenshot Comparison.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Pipeline Screenshot Specification

## Scenarios

### Glass Pipeline Screenshot Comparison

#### glass test page cross-backend

#### glass_dark software vs software_rasterizer produce pixels

- glass_dark software vs software_rasterizer produce pixels
   - Expected: sw.success is true
   - Expected: sw.pixels.len() equals `W * H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("glass_dark software vs software_rasterizer produce pixels")
val html = generate_glass_test_html("glass_dark")
val sw = capture_with_backend(html, W, H, "software")
expect(sw.success).to_equal(true)
expect(sw.pixels.len()).to_equal(W * H)
# Verify non-empty (not all black)
var non_black = 0
var i = 0
while i < sw.pixels.len() and i < 1000:
    if sw.pixels[i] != 0xFF000000:
        non_black = non_black + 1
    i = i + 1
expect(non_black).to_be_greater_than(0)
```

</details>

#### glass_light renders non-empty pixels

- glass_light renders non-empty pixels
   - Expected: sw.success is true
   - Expected: sw.pixels.len() equals `W * H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("glass_light renders non-empty pixels")
val html = generate_glass_test_html("glass_light")
val sw = capture_with_backend(html, W, H, "software")
expect(sw.success).to_equal(true)
expect(sw.pixels.len()).to_equal(W * H)
```

</details>

#### core demos web vs engine pipeline

#### renders both pipelines for a demo

- renders both pipelines for a demo


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders both pipelines for a demo")
# Use a minimal demo if available
val demos = list_core_glass_demos()
if demos.len() > 0:
    val demo = demos[0]
    val output = render_both_pipelines(demo.path, "glass_dark", W, H)
    if output.error == "":
        expect(output.web_pixels.len()).to_be_greater_than(0)
        expect(output.engine_pixels.len()).to_be_greater_than(0)
        val result = compare_pixel_buffers(
            output.web_pixels, output.engine_pixels, W, H, THRESHOLD_PIPELINE)
        expect(result.match_percentage).to_be_greater_than(MIN_PCT_PIPELINE - 1)
        if result.match_percentage < 10000:
            print "Pipeline comparison for {demo.path}:"
            print_comparison_report(result)
```

</details>

#### cross-backend rendering consistency

#### software backend produces same pixels on repeated renders

- software backend produces same pixels on repeated renders
   - Expected: first.success is true
   - Expected: second.success is true
   - Expected: result.match_percentage equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("software backend produces same pixels on repeated renders")
val html = generate_glass_test_html("glass_dark")
val first = capture_with_backend(html, W, H, "software")
val second = capture_with_backend(html, W, H, "software")
expect(first.success).to_equal(true)
expect(second.success).to_equal(true)
# Repeated renders must be deterministic
val result = compare_pixel_buffers(first.pixels, second.pixels, W, H, 0)
expect(result.match_percentage).to_equal(10000)
```

</details>

#### software vs cuda for glass_dark if cuda available

- software vs cuda for glass_dark if cuda available
   - Expected: sw.success is true
   - Expected: cuda.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("software vs cuda for glass_dark if cuda available")
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
expect(result.match_percentage).to_be_greater_than(MIN_PCT_GPU - 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/glass_pipeline_screenshot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Glass Pipeline Screenshot Comparison.
- Glass Pipeline Screenshot Comparison

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

- Canonical SPipe generation for source `aa95e03512f4cd38074c4ff07e1f76dd318b491c1f454120f76110a49f491be1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aa95e03512f4cd38074c4ff07e1f76dd318b491c1f454120f76110a49f491be1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aa95e03512f4cd38074c4ff07e1f76dd318b491c1f454120f76110a49f491be1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/integration/rendering/glass_pipeline_screenshot_spec.spl
mirror: doc/06_spec/integration/rendering/glass_pipeline_screenshot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=75 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/glass_pipeline_screenshot_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/integration/rendering/glass_pipeline_screenshot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/glass_pipeline_screenshot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/glass_pipeline_screenshot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/glass_pipeline_screenshot_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders both pipelines for a demo' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
