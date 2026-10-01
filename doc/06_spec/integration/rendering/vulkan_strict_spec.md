# vulkan_strict_spec

> Purpose: This spec proves Vulkan strict smoke tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_strict_spec

Purpose: This spec proves Vulkan strict smoke tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/vulkan_strict_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Vulkan strict smoke tests.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Vulkan strict smoke tests

#### probe_vulkan device diagnostics

#### probe_vulkan returns a typed BackendProbeResult

- probe_vulkan returns a typed BackendProbeResult
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-VULKANSTRICT-001
step("probe_vulkan returns a typed BackendProbeResult")
val probe = probe_vulkan()
val ok = probe.is_ok() or status_is_terminal_failure(probe)
expect(ok).to_equal(true)
```

</details>

#### probe_vulkan reports requested_name as vulkan

- probe_vulkan reports requested_name as vulkan
- probe_vulkan reports requested_name as vulkan
   - Expected: probe.requested_name equals `vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe_vulkan reports requested_name as vulkan")
step("probe_vulkan reports requested_name as vulkan")
val probe = probe_vulkan()
expect(probe.requested_name).to_equal("vulkan")
```

</details>

#### probe_vulkan on success reports api_name as vulkan

- probe_vulkan on success reports api_name as vulkan
- probe_vulkan on success reports api_name as vulkan
   - Expected: probe.api_name equals `vulkan`
   - Expected: probe.available is true
   - Expected: probe.available is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe_vulkan on success reports api_name as vulkan")
step("probe_vulkan on success reports api_name as vulkan")
# Probe SELF-consistency: the probe's own fields must agree with each
# other. This is a claim about the probe object, not a prediction
# about any later create, so it stays a hard assertion.
val probe = probe_vulkan()
if probe.is_ok():
    expect(probe.api_name).to_equal("vulkan")
    expect(probe.available).to_equal(true)
else:
    expect(probe.available).to_equal(false)
```

</details>

#### probe_vulkan on failure carries non-empty fallback_reason

- probe_vulkan on failure carries non-empty fallback_reason
- probe_vulkan on failure carries non-empty fallback_reason
   - Expected: status_is_terminal_failure(probe) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe_vulkan on failure carries non-empty fallback_reason")
step("probe_vulkan on failure carries non-empty fallback_reason")
val probe = probe_vulkan()
if not probe.is_ok():
    expect(status_is_terminal_failure(probe)).to_equal(true)
    expect(probe.fallback_reason).to_not_equal("")
```

</details>

#### probe_vulkan diagnostic_text is non-empty

- probe_vulkan diagnostic_text is non-empty
- probe_vulkan diagnostic_text is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe_vulkan diagnostic_text is non-empty")
step("probe_vulkan diagnostic_text is non-empty")
val probe = probe_vulkan()
val txt = probe.diagnostic_text()
expect(txt.len()).to_be_greater_than(0)
```

</details>

#### create_with_backend_strict vulkan strictness

#### never hands back a non-vulkan engine

- never hands back a non-vulkan engine
- never hands back a non-vulkan engine
   - Expected: engine.backend_name() equals `vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("never hands back a non-vulkan engine")
step("never hands back a non-vulkan engine")
# The create is attempted REGARDLESS of any probe. Both outcomes owe
# a strictness claim, so neither branch is a silent skip.
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if result.is_ok():
    var engine = result.unwrap()
    expect(engine.backend_name()).to_equal("vulkan")
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("vulkan-strictness", result.unwrap_err())
```

</details>

#### a failed strict create carries a terminal status and the requested name

- a failed strict create carries a terminal status and the requested name
- a failed strict create carries a terminal status and the requested name
   - Expected: status_is_terminal_failure(diag) is true
   - Expected: diag.requested_name equals `vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("a failed strict create carries a terminal status and the requested name")
step("a failed strict create carries a terminal status and the requested name")
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if not result.is_ok():
    val diag = result.unwrap_err()
    expect(status_is_terminal_failure(diag)).to_equal(true)
    expect(diag.requested_name).to_equal("vulkan")
else:
    print "[probe-gpu] vulkan-typed-error: GPU BRANCH SKIPPED — the strict create succeeded, so the failure path was not exercised; this example proves NOTHING about the failure path"
```

</details>

#### a failed strict create carries a non-empty fallback_reason

- a failed strict create carries a non-empty fallback_reason
- a failed strict create carries a non-empty fallback_reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("a failed strict create carries a non-empty fallback_reason")
step("a failed strict create carries a non-empty fallback_reason")
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if not result.is_ok():
    val diag = result.unwrap_err()
    expect(diag.fallback_reason).to_not_equal("")
else:
    print "[probe-gpu] vulkan-fallback-reason: GPU BRANCH SKIPPED — the strict create succeeded, so the failure path was not exercised; this example proves NOTHING about the failure path"
```

</details>

#### create_with_backend_strict vulkan hardware path

#### returns a 16x16 vulkan engine with loaded SPIR-V modules, or a structured failure

- returns a 16x16 vulkan engine with loaded SPIR-V modules, or a structured failure
- returns a 16x16 vulkan engine with loaded SPIR-V modules, or a structure
   - Expected: engine.backend_name() equals `vulkan`
   - Expected: engine.width() equals `16`
   - Expected: engine.height() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a 16x16 vulkan engine with loaded SPIR-V modules, or a structured failure")
step("returns a 16x16 vulkan engine with loaded SPIR-V modules, or a structure")
# This is the one example that measures the probe/create gap: the
# probe answer is DISCLOSED, never asserted. A successful create
# implies every spirv_* blob was accepted by the driver.
val probe = probe_vulkan()
val probe_ready = probe.is_ok()
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
val created = result.is_ok()
_disclose_toctou("vulkan-hardware", probe_ready, created)
if created:
    var engine = result.unwrap()
    expect(engine.backend_name()).to_equal("vulkan")
    expect(engine.width()).to_equal(16)
    expect(engine.height()).to_equal(16)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("vulkan-hardware", result.unwrap_err())
```

</details>

#### clear pixel parity with CPU reference

#### clear fills entire framebuffer with the given color

- clear fills entire framebuffer with the given color
- clear fills entire framebuffer with the given color
   - Expected: pixels[0] equals `fill_color`
   - Expected: pixels[127] equals `fill_color`
   - Expected: pixels[255] equals `fill_color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear fills entire framebuffer with the given color")
step("clear fills entire framebuffer with the given color")
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if result.is_ok():
    var engine = result.unwrap()
    val fill_color = color_blue_u32()
    engine.clear(fill_color)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("vulkan-clear-fill", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("vulkan-clear-fill", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("vulkan-clear-fill", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        # Holds on whatever backend actually served the frame, so it
        # is asserted on every source that produced one, not only on
        # the GPU branch.
        expect(pixels[0]).to_equal(fill_color)
        expect(pixels[127]).to_equal(fill_color)
        expect(pixels[255]).to_equal(fill_color)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("vulkan-clear-fill", result.unwrap_err())
```

</details>

#### clear matches CPU reference pixel-for-pixel

- clear matches CPU reference pixel-for-pixel
- clear matches CPU reference pixel-for-pixel
   - Expected: mismatch_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear matches CPU reference pixel-for-pixel")
step("clear matches CPU reference pixel-for-pixel")
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if result.is_ok():
    var engine = result.unwrap()
    val fill_color = color_blue_u32()
    engine.clear(fill_color)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("vulkan-clear-parity", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("vulkan-clear-parity", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("vulkan-clear-parity", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        var mismatch_count = 0
        var ci = 0
        while ci < 256:
            if pixels[ci] != fill_color:
                mismatch_count = mismatch_count + 1
            ci = ci + 1
        expect(mismatch_count).to_equal(0)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("vulkan-clear-parity", result.unwrap_err())
```

</details>

#### draw_rect_filled pixel parity with CPU reference

#### checked clear and rect return exact device-backed readback before present

- checked clear and rect return exact device-backed readback before present
- checked clear and rect return exact device-backed readback before presen
   - Expected: readback.pixels.len() equals `256`
   - Expected: mismatch_count equals `0`
   - Expected: backend.cpu_fallback_used is false
   - Expected: backend.completion_unknown is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("checked clear and rect return exact device-backed readback before present")
step("checked clear and rect return exact device-backed readback before presen")
# init() is attempted regardless of any probe; the readback decides
# what may be claimed.
var backend = VulkanBackend.create()
val initialized = backend.init(16, 16)
if initialized:
    val bg = color_blue_u32()
    val fg = color_red_u32()
    backend.clear(bg)
    backend.draw_rect_filled(2, 2, 6, 6, fg)
    val readback = backend.read_pixels_with_source()
    _assert_provenance_invariants("vulkan-direct-readback", readback.source,
        readback.backend_handle, readback.device_identity, readback.pixel_count, expected_px())
    _report_outcome("vulkan-direct-readback", readback.source, readback.backend_handle,
        readback.device_identity, readback.pixel_count, expected_px())
    if _source_is_no_frame(readback.source):
        _frame_assertions_skipped("vulkan-direct-readback", readback.source)
    else:
        val cpu_ref = build_cpu_reference(16, 16, bg, fg, 2, 2, 6, 6)
        var mismatch_count = 0
        expect(readback.pixels.len()).to_equal(256)
        if readback.pixels.len() == 256:
            var ci = 0
            while ci < 256:
                if readback.pixels[ci] != cpu_ref[ci]:
                    mismatch_count = mismatch_count + 1
                ci = ci + 1
        expect(mismatch_count).to_equal(0)
    # Backend self-consistency: a device-sourced frame may not also
    # claim a CPU fallback or an unknown completion.
    if readback.source == "device_readback":
        expect(backend.cpu_fallback_used).to_equal(false)
        expect(backend.completion_unknown).to_equal(false)
    backend.shutdown()
else:
    print "[probe-gpu] vulkan-direct-readback: GPU BRANCH SKIPPED — VulkanBackend.init returned false; this example proves NOTHING about the GPU path"
```

</details>

#### draw_rect_filled writes correct pixels in the rect region

- draw_rect_filled writes correct pixels in the rect region
- draw_rect_filled writes correct pixels in the rect region
   - Expected: pixels[6 * 16 + 6] equals `fg`
   - Expected: pixels[0] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_rect_filled writes correct pixels in the rect region")
step("draw_rect_filled writes correct pixels in the rect region")
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    # Clear to blue, draw 4x4 red rect at (4,4)
    engine.clear(bg)
    engine.draw_rect_filled(4, 4, 4, 4, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("vulkan-rect-region", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("vulkan-rect-region", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("vulkan-rect-region", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        # Pixel at (6,6) must be inside the rect (red)
        expect(pixels[6 * 16 + 6]).to_equal(fg)
        # Pixel at (0,0) must be outside rect (blue)
        expect(pixels[0]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("vulkan-rect-region", result.unwrap_err())
```

</details>

#### clear then draw_rect_filled matches CPU reference pixel-for-pixel

- clear then draw_rect_filled matches CPU reference pixel-for-pixel
- clear then draw_rect_filled matches CPU reference pixel-for-pixel
   - Expected: mismatch_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear then draw_rect_filled matches CPU reference pixel-for-pixel")
step("clear then draw_rect_filled matches CPU reference pixel-for-pixel")
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    engine.draw_rect_filled(2, 2, 6, 6, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("vulkan-rect-parity", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("vulkan-rect-parity", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("vulkan-rect-parity", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        # Build CPU reference
        val cpu_ref = build_cpu_reference(16, 16, bg, fg, 2, 2, 6, 6)
        var mismatch_count = 0
        var ci = 0
        while ci < 256:
            if pixels[ci] != cpu_ref[ci]:
                mismatch_count = mismatch_count + 1
            ci = ci + 1
        expect(mismatch_count).to_equal(0)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("vulkan-rect-parity", result.unwrap_err())
```

</details>

#### rect outside framebuffer bounds does not corrupt surrounding pixels

- rect outside framebuffer bounds does not corrupt surrounding pixels
- rect outside framebuffer bounds does not corrupt surrounding pixels
   - Expected: pixels[0] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rect outside framebuffer bounds does not corrupt surrounding pixels")
step("rect outside framebuffer bounds does not corrupt surrounding pixels")
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    # Draw rect that starts at (14,14) with size (8,8) — mostly out of bounds
    engine.draw_rect_filled(14, 14, 8, 8, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("vulkan-rect-bounds", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("vulkan-rect-bounds", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("vulkan-rect-bounds", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        # Pixel at (0,0) must still be blue
        expect(pixels[0]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("vulkan-rect-bounds", result.unwrap_err())
```

</details>

#### sync and readback correctness

#### read_pixels after present reflects latest draw

- read_pixels after present reflects latest draw
- read_pixels after present reflects latest draw
   - Expected: pixels_first[0] equals `first_color`
   - Expected: pixels_second[0] equals `second_color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read_pixels after present reflects latest draw")
step("read_pixels after present reflects latest draw")
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if result.is_ok():
    var engine = result.unwrap()
    val first_color = color_blue_u32()
    val second_color = color_red_u32()
    engine.clear(first_color)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("vulkan-readback-latest", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("vulkan-readback-latest", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("vulkan-readback-latest", drawn.source)
    else:
        engine.present()
        val pixels_first = engine.read_pixels()
        expect(pixels_first[0]).to_equal(first_color)
        engine.clear(second_color)
        engine.present()
        val pixels_second = engine.read_pixels()
        expect(pixels_second[0]).to_equal(second_color)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("vulkan-readback-latest", result.unwrap_err())
```

</details>

#### present idempotent — second present same content

- present idempotent — second present same content
- present idempotent — second present same content
   - Expected: p1[0] equals `p2[0]`
   - Expected: p1[255] equals `p2[255]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("present idempotent — second present same content")
step("present idempotent — second present same content")
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if result.is_ok():
    var engine = result.unwrap()
    val fill_color = color_red_u32()
    engine.clear(fill_color)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("vulkan-present-idempotent", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("vulkan-present-idempotent", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("vulkan-present-idempotent", drawn.source)
    else:
        engine.present()
        val p1 = engine.read_pixels()
        engine.present()
        val p2 = engine.read_pixels()
        expect(p1[0]).to_equal(p2[0])
        expect(p1[255]).to_equal(p2[255])
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("vulkan-present-idempotent", result.unwrap_err())

print "[probe-gpu] RUN VERDICT: this run's GPU evidence is exactly the set of '[probe-gpu] <label>: GPU-PROVEN' lines above."
print "[probe-gpu] RUN VERDICT: every '[probe-gpu] <label>: GPU BRANCH SKIPPED' line marks an example that proves NOTHING about the GPU path."
print "[probe-gpu] RUN VERDICT: a PASS with no GPU-PROVEN line does NOT attest any Vulkan device — read it as 'device unavailable', not as 'Vulkan works'."
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-VULKANSTRICT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fc14b583c7b84070e8060679929e839c61f0ba40a04da5950c4aa29a1b3cba66`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc14b583c7b84070e8060679929e839c61f0ba40a04da5950c4aa29a1b3cba66`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc14b583c7b84070e8060679929e839c61f0ba40a04da5950c4aa29a1b3cba66`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/rendering/vulkan_strict_spec.spl
mirror: doc/06_spec/integration/rendering/vulkan_strict_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/vulkan_strict_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/vulkan_strict_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/vulkan_strict_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/vulkan_strict_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_vulkan returns a typed BackendProbeResult' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/vulkan_strict_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_vulkan reports requested_name as vulkan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/vulkan_strict_spec.spl:198:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_vulkan on success reports api_name as vulkan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
