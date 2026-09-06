# Every call site here is a SUCCESSFUL STRICT cuda create, so the cuda

> Purpose: This spec proves CUDA strict smoke tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Every call site here is a SUCCESSFUL STRICT cuda create, so the cuda

Purpose: This spec proves CUDA strict smoke tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/cuda_strict_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves CUDA strict smoke tests.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### CUDA strict smoke tests

#### probe_cuda device diagnostics

#### probe_cuda returns a typed BackendProbeResult

- probe_cuda returns a typed BackendProbeResult
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-CUDASTRICT-001
step("probe_cuda returns a typed BackendProbeResult")
val probe = probe_cuda()
val ok = probe.is_usable() or status_is_terminal_failure(probe)
expect(ok).to_equal(true)
```

</details>

#### probe_cuda reports requested_name as cuda

- probe_cuda reports requested_name as cuda
- probe_cuda reports requested_name as cuda
   - Expected: probe.requested_name equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe_cuda reports requested_name as cuda")
step("probe_cuda reports requested_name as cuda")
val probe = probe_cuda()
expect(probe.requested_name).to_equal("cuda")
```

</details>

#### probe_cuda on success reports device name and ptx shader_format

- probe_cuda on success reports device name and ptx shader_format
- probe_cuda on success reports device name and ptx shader_format
   - Expected: probe.shader_format equals `ptx`
   - Expected: probe.api_name equals `cuda`
   - Expected: probe.available is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe_cuda on success reports device name and ptx shader_format")
step("probe_cuda on success reports device name and ptx shader_format")
# Probe SELF-consistency: the probe's own fields must agree with
# each other. This is a claim about the probe object, not a
# prediction about any later create, so it stays a hard assertion.
val probe = probe_cuda()
if probe.is_usable():
    expect(probe.device_name).to_not_equal("")
    expect(probe.shader_format).to_equal("ptx")
    expect(probe.api_name).to_equal("cuda")
else:
    expect(probe.available).to_equal(false)
```

</details>

#### probe_cuda on failure carries non-empty fallback_reason

- probe_cuda on failure carries non-empty fallback_reason
- probe_cuda on failure carries non-empty fallback_reason
   - Expected: status_is_terminal_failure(probe) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe_cuda on failure carries non-empty fallback_reason")
step("probe_cuda on failure carries non-empty fallback_reason")
val probe = probe_cuda()
if not probe.is_usable():
    expect(status_is_terminal_failure(probe)).to_equal(true)
    expect(probe.fallback_reason).to_not_equal("")
```

</details>

#### probe_cuda diagnostic_text is non-empty

- probe_cuda diagnostic_text is non-empty
- probe_cuda diagnostic_text is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe_cuda diagnostic_text is non-empty")
step("probe_cuda diagnostic_text is non-empty")
val probe = probe_cuda()
val txt = probe.diagnostic_text()
expect(txt.len()).to_be_greater_than(0)
```

</details>

#### probe_cuda never substitutes a different backend under the cuda name

- probe_cuda never substitutes a different backend under the cuda name
- probe_cuda never substitutes a different backend under the cuda name
   - Expected: probe.selected_name == "cpu" or probe.selected_name == "software" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probe_cuda never substitutes a different backend under the cuda name")
step("probe_cuda never substitutes a different backend under the cuda name")
val probe = probe_cuda()
expect(probe.selected_name == "cpu" or probe.selected_name == "software").to_equal(false)
```

</details>

#### create_with_backend_strict cuda failure path

#### a failed strict create carries a terminal status and the requested name

- a failed strict create carries a terminal status and the requested name
- a failed strict create carries a terminal status and the requested name
   - Expected: status_is_terminal_failure(diag) is true
   - Expected: diag.requested_name equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("a failed strict create carries a terminal status and the requested name")
step("a failed strict create carries a terminal status and the requested name")
# The create is attempted REGARDLESS of any probe. The OLD version
# asserted `result.is_ok()` MUST be FALSE because the probe had said
# unusable — the pessimistic half of the TOCTOU, which false-reds
# the moment the create succeeds where the probe predicted failure.
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if not result.is_ok():
    val diag = result.unwrap_err()
    expect(status_is_terminal_failure(diag)).to_equal(true)
    expect(diag.requested_name).to_equal("cuda")
else:
    print "[cuda-gpu] cuda-typed-error: GPU BRANCH SKIPPED — the strict create succeeded, so the failure path was not exercised; this example proves NOTHING about the failure path"
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
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if not result.is_ok():
    val diag = result.unwrap_err()
    expect(diag.fallback_reason).to_not_equal("")
else:
    print "[cuda-gpu] cuda-fallback-reason: GPU BRANCH SKIPPED — the strict create succeeded, so the failure path was not exercised; this example proves NOTHING about the failure path"
```

</details>

#### create_with_backend_strict cuda hardware path

#### never hands back a non-cuda engine

- never hands back a non-cuda engine
- never hands back a non-cuda engine
   - Expected: engine.backend_name() equals `cuda`
   - Expected: engine.width() equals `16`
   - Expected: engine.height() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("never hands back a non-cuda engine")
step("never hands back a non-cuda engine")
# Both outcomes owe a strictness claim, so neither branch is a
# silent skip.
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    expect(engine.backend_name()).to_equal("cuda")
    expect(engine.width()).to_equal(16)
    expect(engine.height()).to_equal(16)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-strictness", result.unwrap_err())
```

</details>

#### the probe/create divergence is disclosed, never asserted

- the probe/create divergence is disclosed, never asserted
- the probe/create divergence is disclosed, never asserted
   - Expected: engine.backend_name() equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("the probe/create divergence is disclosed, never asserted")
step("the probe/create divergence is disclosed, never asserted")
# This is the one example that measures the probe/create gap: the
# probe answer is DISCLOSED, never asserted.
val probe = probe_cuda()
val probe_ready = probe.is_usable()
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
val created = result.is_ok()
_disclose_toctou("cuda-hardware", probe_ready, created)
if created:
    var engine = result.unwrap()
    expect(engine.backend_name()).to_equal("cuda")
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-hardware", result.unwrap_err())
```

</details>

#### PTX kernel: clear and readback

#### clear to red produces all-red pixels

- clear to red produces all-red pixels
- clear to red produces all-red pixels
   - Expected: pixels.len() equals `256`
   - Expected: all_red is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear to red produces all-red pixels")
step("clear to red produces all-red pixels")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val red = color_red_u32()
    engine.clear(red)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-clear-red", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-clear-red", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-clear-red", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        var all_red = true
        var idx = 0
        while idx < 256:
            if pixels[idx] != red:
                all_red = false
            idx = idx + 1
        expect(all_red).to_equal(true)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-clear-red", result.unwrap_err())
```

</details>

#### draw_rect_filled writes correct pixels in the rect region

- draw_rect_filled writes correct pixels in the rect region
- draw_rect_filled writes correct pixels in the rect region
   - Expected: pixels.len() equals `256`
   - Expected: pixels[6 * 16 + 6] equals `fg`
   - Expected: pixels[0] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_rect_filled writes correct pixels in the rect region")
step("draw_rect_filled writes correct pixels in the rect region")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    # Clear to blue, draw 4x4 red rect at (4,4)
    engine.clear(bg)
    engine.draw_rect_filled(4, 4, 4, 4, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-rect-filled", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-rect-filled", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-rect-filled", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        # Pixel at (6,6) inside rect must be red
        expect(pixels[6 * 16 + 6]).to_equal(fg)
        # Pixel at (0,0) outside rect must be blue
        expect(pixels[0]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-rect-filled", result.unwrap_err())
```

</details>

#### draw_rect writes only the outline pixels

- draw_rect writes only the outline pixels
- draw_rect writes only the outline pixels
   - Expected: pixels.len() equals `256`
   - Expected: pixels[4 * 16 + 4] equals `fg`
   - Expected: pixels[4 * 16 + 9] equals `fg`
   - Expected: pixels[8 * 16 + 4] equals `fg`
   - Expected: pixels[8 * 16 + 9] equals `fg`
   - Expected: pixels[6 * 16 + 6] equals `bg`
   - Expected: pixels[0] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_rect writes only the outline pixels")
step("draw_rect writes only the outline pixels")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    engine.draw_rect(4, 4, 6, 5, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-rect-outline", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-rect-outline", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-rect-outline", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[4 * 16 + 4]).to_equal(fg)
        expect(pixels[4 * 16 + 9]).to_equal(fg)
        expect(pixels[8 * 16 + 4]).to_equal(fg)
        expect(pixels[8 * 16 + 9]).to_equal(fg)
        expect(pixels[6 * 16 + 6]).to_equal(bg)
        expect(pixels[0]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-rect-outline", result.unwrap_err())
```

</details>

#### draw_line writes line pixels through the CUDA framebuffer

- draw_line writes line pixels through the CUDA framebuffer
- draw_line writes line pixels through the CUDA framebuffer
   - Expected: pixels.len() equals `256`
   - Expected: pixels[2 * 16 + 2] equals `fg`
   - Expected: pixels[2 * 16 + 3] equals `fg`
   - Expected: pixels[2 * 16 + 4] equals `fg`
   - Expected: pixels[2 * 16 + 5] equals `fg`
   - Expected: pixels[2 * 16 + 6] equals `fg`
   - Expected: pixels[3 * 16 + 2] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_line writes line pixels through the CUDA framebuffer")
step("draw_line writes line pixels through the CUDA framebuffer")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    engine.draw_line(2, 2, 6, 2, fg, 1)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-line", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-line", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-line", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[2 * 16 + 2]).to_equal(fg)
        expect(pixels[2 * 16 + 3]).to_equal(fg)
        expect(pixels[2 * 16 + 4]).to_equal(fg)
        expect(pixels[2 * 16 + 5]).to_equal(fg)
        expect(pixels[2 * 16 + 6]).to_equal(fg)
        expect(pixels[3 * 16 + 2]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-line", result.unwrap_err())
```

</details>

#### draw_circle writes outline pixels through the CUDA framebuffer

- draw_circle writes outline pixels through the CUDA framebuffer
- draw_circle writes outline pixels through the CUDA framebuffer
   - Expected: pixels.len() equals `256`
   - Expected: pixels[8 * 16 + 11] equals `fg`
   - Expected: pixels[8 * 16 + 5] equals `fg`
   - Expected: pixels[11 * 16 + 8] equals `fg`
   - Expected: pixels[5 * 16 + 8] equals `fg`
   - Expected: pixels[8 * 16 + 8] equals `bg`
   - Expected: pixels[0] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_circle writes outline pixels through the CUDA framebuffer")
step("draw_circle writes outline pixels through the CUDA framebuffer")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    engine.draw_circle(8, 8, 3, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-circle", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-circle", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-circle", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[8 * 16 + 11]).to_equal(fg)
        expect(pixels[8 * 16 + 5]).to_equal(fg)
        expect(pixels[11 * 16 + 8]).to_equal(fg)
        expect(pixels[5 * 16 + 8]).to_equal(fg)
        expect(pixels[8 * 16 + 8]).to_equal(bg)
        expect(pixels[0]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-circle", result.unwrap_err())
```

</details>

#### draw_circle_filled writes filled pixels through the CUDA framebuffer

- draw_circle_filled writes filled pixels through the CUDA framebuffer
- draw_circle_filled writes filled pixels through the CUDA framebuffer
   - Expected: pixels.len() equals `256`
   - Expected: pixels[8 * 16 + 8] equals `fg`
   - Expected: pixels[8 * 16 + 11] equals `fg`
   - Expected: pixels[8 * 16 + 5] equals `fg`
   - Expected: pixels[11 * 16 + 8] equals `fg`
   - Expected: pixels[5 * 16 + 8] equals `fg`
   - Expected: pixels[4 * 16 + 4] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_circle_filled writes filled pixels through the CUDA framebuffer")
step("draw_circle_filled writes filled pixels through the CUDA framebuffer")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    engine.draw_circle_filled(8, 8, 3, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-circle-filled", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-circle-filled", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-circle-filled", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[8 * 16 + 8]).to_equal(fg)
        expect(pixels[8 * 16 + 11]).to_equal(fg)
        expect(pixels[8 * 16 + 5]).to_equal(fg)
        expect(pixels[11 * 16 + 8]).to_equal(fg)
        expect(pixels[5 * 16 + 8]).to_equal(fg)
        expect(pixels[4 * 16 + 4]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-circle-filled", result.unwrap_err())
```

</details>

#### draw_rounded_rect writes rounded fill through the CUDA framebuffer

- draw_rounded_rect writes rounded fill through the CUDA framebuffer
- draw_rounded_rect writes rounded fill through the CUDA framebuffer
   - Expected: pixels.len() equals `256`
   - Expected: pixels[4 * 16 + 4] equals `bg`
   - Expected: pixels[4 * 16 + 5] equals `bg`
   - Expected: pixels[4 * 16 + 6] equals `fg`
   - Expected: pixels[6 * 16 + 4] equals `fg`
   - Expected: pixels[6 * 16 + 8] equals `fg`
   - Expected: pixels[9 * 16 + 11] equals `bg`
   - Expected: pixels[0] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_rounded_rect writes rounded fill through the CUDA framebuffer")
step("draw_rounded_rect writes rounded fill through the CUDA framebuffer")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    engine.draw_rounded_rect(4, 4, 8, 6, 2, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-rounded-rect", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-rounded-rect", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-rounded-rect", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[4 * 16 + 4]).to_equal(bg)
        expect(pixels[4 * 16 + 5]).to_equal(bg)
        expect(pixels[4 * 16 + 6]).to_equal(fg)
        expect(pixels[6 * 16 + 4]).to_equal(fg)
        expect(pixels[6 * 16 + 8]).to_equal(fg)
        expect(pixels[9 * 16 + 11]).to_equal(bg)
        expect(pixels[0]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-rounded-rect", result.unwrap_err())
```

</details>

#### draw_triangle_filled writes filled pixels through the CUDA framebuffer

- draw_triangle_filled writes filled pixels through the CUDA framebuffer
- draw_triangle_filled writes filled pixels through the CUDA framebuffer
   - Expected: pixels.len() equals `256`
   - Expected: pixels[4 * 16 + 4] equals `fg`
   - Expected: pixels[4 * 16 + 10] equals `fg`
   - Expected: pixels[10 * 16 + 4] equals `fg`
   - Expected: pixels[5 * 16 + 5] equals `fg`
   - Expected: pixels[6 * 16 + 6] equals `fg`
   - Expected: pixels[10 * 16 + 10] equals `bg`
   - Expected: pixels[3 * 16 + 4] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_triangle_filled writes filled pixels through the CUDA framebuffer")
step("draw_triangle_filled writes filled pixels through the CUDA framebuffer")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    engine.draw_triangle_filled(4, 4, 10, 4, 4, 10, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-triangle", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-triangle", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-triangle", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[4 * 16 + 4]).to_equal(fg)
        expect(pixels[4 * 16 + 10]).to_equal(fg)
        expect(pixels[10 * 16 + 4]).to_equal(fg)
        expect(pixels[5 * 16 + 5]).to_equal(fg)
        expect(pixels[6 * 16 + 6]).to_equal(fg)
        expect(pixels[10 * 16 + 10]).to_equal(bg)
        expect(pixels[3 * 16 + 4]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-triangle", result.unwrap_err())
```

</details>

#### clear then draw_rect_filled matches CPU reference pixel-for-pixel

- clear then draw_rect_filled matches CPU reference pixel-for-pixel
- clear then draw_rect_filled matches CPU reference pixel-for-pixel
   - Expected: mismatch_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear then draw_rect_filled matches CPU reference pixel-for-pixel")
step("clear then draw_rect_filled matches CPU reference pixel-for-pixel")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    engine.draw_rect_filled(2, 2, 6, 6, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-cpu-parity", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-cpu-parity", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-cpu-parity", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        var mismatch_count = 0
        var ci = 0
        while ci < 256:
            val px = ci % 16
            val py = ci / 16
            val expected = if px >= 2 and px < 8 and py >= 2 and py < 8: fg else: bg
            if pixels[ci] != expected:
                mismatch_count = mismatch_count + 1
            ci = ci + 1
        expect(mismatch_count).to_equal(0)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-cpu-parity", result.unwrap_err())
```

</details>

#### draw_image writes uploaded pixels through the CUDA framebuffer

- draw_image writes uploaded pixels through the CUDA framebuffer
- draw_image writes uploaded pixels through the CUDA framebuffer
   - Expected: pixels.len() equals `256`
   - Expected: mismatch_count equals `0`
   - Expected: pixels[0] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_image writes uploaded pixels through the CUDA framebuffer")
step("draw_image writes uploaded pixels through the CUDA framebuffer")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val img0 = 0x01020304 as u32
    val img1 = 0x05060708 as u32
    val img2 = 0x11121314 as u32
    val img3 = 0x15161718 as u32
    engine.clear(bg)
    engine.draw_image(5, 6, 2, 2, [img0, img1, img2, img3])
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-draw-image", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-draw-image", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-draw-image", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        var mismatch_count = 0
        if pixels[6 * 16 + 5] != img0:
            mismatch_count = mismatch_count + 1
        if pixels[6 * 16 + 6] != img1:
            mismatch_count = mismatch_count + 1
        if pixels[7 * 16 + 5] != img2:
            mismatch_count = mismatch_count + 1
        if pixels[7 * 16 + 6] != img3:
            mismatch_count = mismatch_count + 1
        expect(mismatch_count).to_equal(0)
        expect(pixels[0]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-draw-image", result.unwrap_err())
```

</details>

#### draw_gradient_rect writes interpolated rows through the CUDA framebuffer

- draw_gradient_rect writes interpolated rows through the CUDA framebuffer
- draw_gradient_rect writes interpolated rows through the CUDA framebuffer
   - Expected: pixels.len() equals `256`
   - Expected: mismatch_count equals `0`
   - Expected: pixels[0] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_gradient_rect writes interpolated rows through the CUDA framebuffer")
step("draw_gradient_rect writes interpolated rows through the CUDA framebuffer")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val top = 0xFF000000 as u32
    val bottom = 0xFF0F1E2D as u32
    engine.clear(bg)
    engine.draw_gradient_rect(3, 4, 5, 4, top, bottom)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-gradient", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-gradient", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-gradient", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        val mid1 = 0xFF050A0F as u32
        val mid2 = 0xFF0A141E as u32
        var mismatch_count = 0
        var row = 0
        while row < 4:
            val expected = if row == 0: top else: if row == 1: mid1 else: if row == 2: mid2 else: bottom
            var col = 0
            while col < 5:
                if pixels[(4 + row) * 16 + 3 + col] != expected:
                    mismatch_count = mismatch_count + 1
                col = col + 1
            row = row + 1
        expect(mismatch_count).to_equal(0)
        expect(pixels[0]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-gradient", result.unwrap_err())
```

</details>

#### draw_text and clip and mask device readback

#### draw_text result is visible in device readback

- draw_text result is visible in device readback
- draw_text result is visible in device readback
   - Expected: cuda_pixels.len() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_text result is visible in device readback")
step("draw_text result is visible in device readback")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    engine.clear(bg)
    engine.draw_text(0, 0, "X", color_red_u32(), 8)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-draw-text", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-draw-text", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-draw-text", drawn.source)
    else:
        engine.present()
        val cuda_pixels = engine.read_pixels()
        expect(cuda_pixels.len()).to_equal(256)
        var non_bg = 0
        var idx = 0
        while idx < 256:
            if cuda_pixels[idx] != bg:
                non_bg = non_bg + 1
            idx = idx + 1
        expect(non_bg).to_be_greater_than(0)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-draw-text", result.unwrap_err())
```

</details>

#### set_clip constrains draw_rect_filled visible via device readback

- set_clip constrains draw_rect_filled visible via device readback
- set_clip constrains draw_rect_filled visible via device readback
   - Expected: pixels.len() equals `256`
   - Expected: pixels[0] equals `fg`
   - Expected: pixels[3 * 16 + 3] equals `fg`
   - Expected: pixels[4 * 16 + 4] equals `bg`
   - Expected: pixels[15 * 16 + 15] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("set_clip constrains draw_rect_filled visible via device readback")
step("set_clip constrains draw_rect_filled visible via device readback")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    engine.set_clip(0, 0, 4, 4)
    engine.draw_rect_filled(0, 0, 16, 16, fg)
    engine.clear_clip()
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-set-clip", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-set-clip", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-set-clip", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[0]).to_equal(fg)
        expect(pixels[3 * 16 + 3]).to_equal(fg)
        expect(pixels[4 * 16 + 4]).to_equal(bg)
        expect(pixels[15 * 16 + 15]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-set-clip", result.unwrap_err())
```

</details>

#### clear_clip restores full-surface drawing via device readback

- clear_clip restores full-surface drawing via device readback
- clear_clip restores full-surface drawing via device readback
   - Expected: pixels.len() equals `256`
   - Expected: pixels[15 * 16 + 15] equals `fg`
   - Expected: pixels[0] equals `fg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear_clip restores full-surface drawing via device readback")
step("clear_clip restores full-surface drawing via device readback")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    engine.set_clip(0, 0, 2, 2)
    engine.clear_clip()
    engine.draw_rect_filled(0, 0, 16, 16, fg)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-clear-clip", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-clear-clip", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-clear-clip", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[15 * 16 + 15]).to_equal(fg)
        expect(pixels[0]).to_equal(fg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-clear-clip", result.unwrap_err())
```

</details>

#### set_mask constrains draw_rect_filled visible via device readback

- set_mask constrains draw_rect_filled visible via device readback
- set_mask constrains draw_rect_filled visible via device readback
   - Expected: pixels.len() equals `256`
   - Expected: pixels[0] equals `fg`
   - Expected: pixels[1] equals `bg`
   - Expected: pixels[16] equals `fg`
   - Expected: pixels[17] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("set_mask constrains draw_rect_filled visible via device readback")
step("set_mask constrains draw_rect_filled visible via device readback")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val bg = color_blue_u32()
    val fg = color_red_u32()
    engine.clear(bg)
    # mask_buf[i]==0 means blocked; 1 means allowed
    # mask layout [col0_row0, col1_row0, col0_row1, col1_row1]
    # pixel (0,0)=1(pass), (1,0)=0(block), (0,1)=1(pass), (1,1)=0(block)
    engine.set_mask([1u8, 0u8, 1u8, 0u8], 2, 2)
    engine.draw_rect_filled(0, 0, 2, 2, fg)
    engine.clear_mask()
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-set-mask", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-set-mask", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-set-mask", drawn.source)
    else:
        engine.present()
        val pixels = engine.read_pixels()
        expect(pixels.len()).to_equal(256)
        expect(pixels[0]).to_equal(fg)
        expect(pixels[1]).to_equal(bg)
        expect(pixels[16]).to_equal(fg)
        expect(pixels[17]).to_equal(bg)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-set-mask", result.unwrap_err())
```

</details>

#### sync and readback correctness

#### read_pixels after present reflects latest draw

- read_pixels after present reflects latest draw
- read_pixels after present reflects latest draw
   - Expected: first_pixels[0] equals `first_color`
   - Expected: second_pixels[0] equals `second_color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read_pixels after present reflects latest draw")
step("read_pixels after present reflects latest draw")
val result = Engine2D.create_with_backend_strict(16, 16, "cuda")
if result.is_ok():
    var engine = result.unwrap()
    val first_color = color_blue_u32()
    val second_color = color_red_u32()
    engine.clear(first_color)
    val drawn = engine.read_pixels_with_source()
    _assert_provenance_invariants("cuda-readback-latest", drawn.source,
        drawn.backend_handle, drawn.device_identity, drawn.pixel_count, expected_px())
    _report_outcome("cuda-readback-latest", drawn.source, drawn.backend_handle,
        drawn.device_identity, drawn.pixel_count, expected_px())
    if _source_is_no_frame(drawn.source):
        _frame_assertions_skipped("cuda-readback-latest", drawn.source)
    else:
        engine.present()
        val first_pixels = engine.read_pixels()
        engine.clear(second_color)
        engine.present()
        val second_pixels = engine.read_pixels()
        expect(first_pixels[0]).to_equal(first_color)
        expect(second_pixels[0]).to_equal(second_color)
    engine.shutdown()
else:
    _assert_strict_failure_is_structured("cuda-readback-latest", result.unwrap_err())

print "[cuda-gpu] RUN VERDICT: this run's GPU evidence is exactly the set of '[cuda-gpu] <label>: GPU-PROVEN' lines above."
print "[cuda-gpu] RUN VERDICT: every '[cuda-gpu] <label>: GPU BRANCH SKIPPED' line marks an example that proves NOTHING about the GPU path."
print "[cuda-gpu] RUN VERDICT: a PASS with no GPU-PROVEN line does NOT attest any CUDA device — read it as 'device unavailable', not as 'CUDA works'."
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-CUDASTRICT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42674bab79d66faff227992bdd8d3147b4d8e839c389853a17434b71fb3568cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42674bab79d66faff227992bdd8d3147b4d8e839c389853a17434b71fb3568cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42674bab79d66faff227992bdd8d3147b4d8e839c389853a17434b71fb3568cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/rendering/cuda_strict_spec.spl
mirror: doc/06_spec/integration/rendering/cuda_strict_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/cuda_strict_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/cuda_strict_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/cuda_strict_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/cuda_strict_spec.spl:204:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_cuda returns a typed BackendProbeResult' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/cuda_strict_spec.spl:211:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_cuda reports requested_name as cuda' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/cuda_strict_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_cuda on success reports device name and ptx shader_format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
