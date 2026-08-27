# backend_screenshot_compare_spec

> Purpose: This spec proves Backend Screenshot Comparison.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_screenshot_compare_spec

Purpose: This spec proves Backend Screenshot Comparison.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/backend_screenshot_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Backend Screenshot Comparison.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Backend Screenshot Comparison

#### Software vs CPU deterministic buffers

#### compares glass_dark exactly

- compares glass_dark exactly
   - Expected: sw.success is true
   - Expected: cpu.success is true
   - Expected: result.match_percentage equals `MIN_IDENTICAL`
   - Expected: result.passed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BACKENDSCREENSHOTCOMPARE-001
step("compares glass_dark exactly")
val sw = capture_fixture_backend("software", "glass_dark")
val cpu = capture_fixture_backend("cpu", "glass_dark")
expect(sw.success).to_equal(true)
expect(cpu.success).to_equal(true)
val result = compare_exact(sw.pixels, cpu.pixels, W, H)
expect(result.match_percentage).to_equal(MIN_IDENTICAL)
expect(result.passed).to_equal(true)
```

</details>

#### compares glass_light exactly

- compares glass_light exactly
- compares glass_light exactly
   - Expected: sw.success is true
   - Expected: cpu.success is true
   - Expected: result.match_percentage equals `MIN_IDENTICAL`
   - Expected: result.passed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compares glass_light exactly")
step("compares glass_light exactly")
val sw = capture_fixture_backend("software", "glass_light")
val cpu = capture_fixture_backend("cpu", "glass_light")
expect(sw.success).to_equal(true)
expect(cpu.success).to_equal(true)
val result = compare_exact(sw.pixels, cpu.pixels, W, H)
expect(result.match_percentage).to_equal(MIN_IDENTICAL)
expect(result.passed).to_equal(true)
```

</details>

#### Thresholded backend-like buffers

#### keeps near-channel differences within GPU tolerance

- keeps near-channel differences within GPU tolerance
- keeps near-channel differences within GPU tolerance
   - Expected: result.exact_match is false
   - Expected: result.passed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps near-channel differences within GPU tolerance")
step("keeps near-channel differences within GPU tolerance")
val sw = capture_fixture_backend("software", "stress")
val gpu_cap = BackendCapture(
    backend_name: "gpu_like",
    pixels: _near_buffer(0xFF2563EBu32, 0xFF2765EDu32, W * H),
    success: true,
    error: ""
)
val result = compare_pixel_buffers(sw.pixels, gpu_cap.pixels, W, H, THRESHOLD_GPU)
expect(result.match_percentage).to_be_greater_than(MIN_GPU - 1)
expect(result.exact_match).to_equal(false)
expect(result.passed).to_equal(true)
```

</details>

#### reports buffer size mismatches as failed comparisons

- reports buffer size mismatches as failed comparisons
- reports buffer size mismatches as failed comparisons
   - Expected: result.passed is false
   - Expected: result.match_percentage equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports buffer size mismatches as failed comparisons")
step("reports buffer size mismatches as failed comparisons")
val a = _solid_buffer(0xFF000000u32, W * H)
val b = _solid_buffer(0xFF000000u32, (W * H) - 1)
val result = compare_pixel_buffers(a, b, W, H, THRESHOLD_GPU)
expect(result.passed).to_equal(false)
expect(result.match_percentage).to_equal(0)
```

</details>

#### reports invalid dimensions as failed comparisons

- reports invalid dimensions as failed comparisons
- reports invalid dimensions as failed comparisons
   - Expected: result.exact_match is false
   - Expected: result.passed is false
   - Expected: result.match_percentage equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports invalid dimensions as failed comparisons")
step("reports invalid dimensions as failed comparisons")
val result = compare_pixel_buffers([], [], 0, H, THRESHOLD_GPU)
expect(result.exact_match).to_equal(false)
expect(result.passed).to_equal(false)
expect(result.match_percentage).to_equal(0)
```

</details>

#### keeps invalid dimensions failed through profile comparison

- keeps invalid dimensions failed through profile comparison
- keeps invalid dimensions failed through profile comparison
   - Expected: result.exact_match is false
   - Expected: result.passed is false
   - Expected: result.match_percentage equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps invalid dimensions failed through profile comparison")
step("keeps invalid dimensions failed through profile comparison")
val result = compare_with_profile([], [], 0, H, profile_strict())
expect(result.exact_match).to_equal(false)
expect(result.passed).to_equal(false)
expect(result.match_percentage).to_equal(0)
```

</details>

#### Diff image generation

#### produces all-green for identical buffers

- produces all-green for identical buffers
- produces all-green for identical buffers
   - Expected: diff.len() equals `size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces all-green for identical buffers")
step("produces all-green for identical buffers")
val size = 10 * 10
val buf_a = _solid_buffer(0xFF336699u32, size)
val buf_b = _solid_buffer(0xFF336699u32, size)
val diff = generate_diff_image(buf_a, buf_b, 10, 10)
expect(diff.len()).to_equal(size)
val first = diff[0]
val green = ((first >> 8) & 0xFF).to_i32()
val red = ((first >> 16) & 0xFF).to_i32()
expect(green).to_be_greater_than(red)
```

</details>

#### produces red pixels for differing regions

- produces red pixels for differing regions
- produces red pixels for differing regions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces red pixels for differing regions")
step("produces red pixels for differing regions")
val buf_a = _solid_buffer(0xFF000000u32, 100)
val buf_b = _solid_buffer(0xFFFFFFFFu32, 100)
val diff = generate_diff_image(buf_a, buf_b, 10, 10)
val first = diff[0]
val red = ((first >> 16) & 0xFF).to_i32()
expect(red).to_be_greater_than(100)
```

</details>

#### keeps viewport-sized diagnostics for truncated buffers

- keeps viewport-sized diagnostics for truncated buffers
- keeps viewport-sized diagnostics for truncated buffers
   - Expected: diff.len() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps viewport-sized diagnostics for truncated buffers")
step("keeps viewport-sized diagnostics for truncated buffers")
val buf_a = _solid_buffer(0xFF000000u32, 100)
val buf_b = _solid_buffer(0xFF000000u32, 99)
val diff = generate_diff_image(buf_a, buf_b, 10, 10)
expect(diff.len()).to_equal(100)
val last = diff[99]
val red = ((last >> 16) & 0xFF).to_i32()
val green = ((last >> 8) & 0xFF).to_i32()
expect(red).to_be_greater_than(green)
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-BACKENDSCREENSHOTCOMPARE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e51520ba0b2710185a518ce9a1d8da8db38f91575f016f705e514d5eda5c53f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e51520ba0b2710185a518ce9a1d8da8db38f91575f016f705e514d5eda5c53f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e51520ba0b2710185a518ce9a1d8da8db38f91575f016f705e514d5eda5c53f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/02_integration/rendering/backend_screenshot_compare_spec.spl
mirror: doc/06_spec/02_integration/rendering/backend_screenshot_compare_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/backend_screenshot_compare_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/02_integration/rendering/backend_screenshot_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/backend_screenshot_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/backend_screenshot_compare_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/backend_screenshot_compare_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports buffer size mismatches as failed comparisons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/backend_screenshot_compare_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports invalid dimensions as failed comparisons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/backend_screenshot_compare_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps invalid dimensions failed through profile comparison' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
