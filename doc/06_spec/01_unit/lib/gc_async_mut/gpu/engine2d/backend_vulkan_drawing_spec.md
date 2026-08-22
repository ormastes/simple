# backend_vulkan_drawing_spec

> Verifies the backend vulkan drawing behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_vulkan_drawing_spec

Verifies the backend vulkan drawing behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the backend vulkan drawing behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Vulkan 2D drawing lane — SPIR-V parity evidence

#### probe shader format

#### vulkan_spirv_probe reports spirv shader_format (never glsl)

- Verify: vulkan_spirv_probe reports spirv shader_format (never glsl)
   - Expected: probe.shader_format equals `spirv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: vulkan_spirv_probe reports spirv shader_format (never glsl)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val probe = vulkan_spirv_probe()
# The probe always returns spirv format regardless of device state.
expect(probe.shader_format).to_equal("spirv")
```

</details>

#### probe backend_name is vulkan

- Verify: probe backend_name is vulkan
   - Expected: probe.backend_name equals `vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: probe backend_name is vulkan")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val probe = vulkan_spirv_probe()
expect(probe.backend_name).to_equal("vulkan")
```

</details>

#### probe api_name is vulkan

- Verify: probe api_name is vulkan
   - Expected: probe.api_name equals `vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: probe api_name is vulkan")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val probe = vulkan_spirv_probe()
expect(probe.api_name).to_equal("vulkan")
```

</details>

#### probe returns Initialized or Failed — no intermediate state

- Verify: probe returns Initialized or Failed — no intermediate state
   - Expected: probe.status.to_text() equals `Initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: probe returns Initialized or Failed — no intermediate state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val probe = vulkan_spirv_probe()
# available must match Initialized status
if probe.available:
    expect(probe.status.to_text()).to_equal("Initialized")
else:
    # Failed probes must carry a non-empty reason
    expect(probe.fallback_reason.len()).to_be_greater_than(0)
```

</details>

### Vulkan 2D drawing lane — VulkanSessionBackend lifecycle

#### creation and init

#### create returns uninitialised session with initialized=false

- Verify: create returns uninitialised session with initialized=false
   - Expected: s.device_name equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: create returns uninitialised session with initialized=false")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val s = VulkanSessionBackend.create("default")
assert_false(s.initialized)
expect(s.device_name).to_equal("none")
```

</details>

#### create sets last_error to empty

- Verify: create sets last_error to empty
   - Expected: s.last_error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: create sets last_error to empty")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val s = VulkanSessionBackend.create("default")
expect(s.last_error).to_equal("")
```

</details>

#### session counters start at zero

- Verify: session counters start at zero
   - Expected: s.clear_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: s.rect_count equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: session counters start at zero")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val s = VulkanSessionBackend.create("default")
expect(s.clear_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(s.rect_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### operations before init return not-initialized error

- Verify: operations before init return not-initialized error
   - Expected: err equals `not initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: operations before init return not-initialized error")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var s = VulkanSessionBackend.create("default")
val err = s.clear(0, 0, 0, 255)
expect(err).to_equal("not initialized")
```

</details>

#### draw_rect before init returns not-initialized error

- Verify: draw_rect before init returns not-initialized error
   - Expected: err equals `not initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: draw_rect before init returns not-initialized error")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var s = VulkanSessionBackend.create("default")
val err = s.draw_rect(0, 0, 10, 10, 0xFF0000FF)
expect(err).to_equal("not initialized")
```

</details>

#### init lifecycle — pre-init state

#### session_mode is stored from create

- Verify: session_mode is stored from create
   - Expected: s.session_mode equals `headless`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: session_mode is stored from create")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val s = VulkanSessionBackend.create("headless")
expect(s.session_mode).to_equal("headless")
```

</details>

#### create with different modes stores correct mode

- Verify: create with different modes stores correct mode
   - Expected: s1.session_mode equals `default`
   - Expected: s2.session_mode equals `strict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: create with different modes stores correct mode")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val s1 = VulkanSessionBackend.create("default")
val s2 = VulkanSessionBackend.create("strict")
expect(s1.session_mode).to_equal("default")
expect(s2.session_mode).to_equal("strict")
```

</details>

#### uninit clear returns not-initialized error string

- Verify: uninit clear returns not-initialized error string
   - Expected: e1 equals `not initialized`
   - Expected: e2 equals `not initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: uninit clear returns not-initialized error string")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var s = VulkanSessionBackend.create("default")
# Each call before init_device returns "not initialized"
val e1 = s.clear(0, 0, 0, 255)
val e2 = s.clear(128, 128, 128, 255)
expect(e1).to_equal("not initialized")
expect(e2).to_equal("not initialized")
```

</details>

#### clear_count stays at 0 when not initialized

- Verify: clear_count stays at 0 when not initialized
   - Expected: s.clear_count equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: clear_count stays at 0 when not initialized")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var s = VulkanSessionBackend.create("default")
s.clear(0, 0, 0, 255)
s.clear(255, 255, 255, 255)
expect(s.clear_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### rect_count stays at 0 when not initialized

- Verify: rect_count stays at 0 when not initialized
   - Expected: s.rect_count equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: rect_count stays at 0 when not initialized")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var s = VulkanSessionBackend.create("default")
s.draw_rect(0, 0, 10, 10, 0xFFFFFFFF)
expect(s.rect_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### Vulkan 2D drawing lane — VulkanBackend raster

#### exact framebuffer byte decoding

#### rejects empty, short, and overlong device buffers before indexing

- Verify: rejects empty, short, and overlong device buffers before indexing
- Decode only one exact little-endian ARGB pixel
   - Expected: _bytes_to_pixel_array([], 0) equals `[]`
   - Expected: _bytes_to_pixel_array([], 1) equals `[]`
   - Expected: _bytes_to_pixel_array([0x44u8, 0x33u8, 0x22u8], 1) equals `[]`
   - Expected: _bytes_to_pixel_array([0x44u8, 0x33u8, 0x22u8, 0x11u8, 0x00u8], 1) equals `[]`
   - Expected: _bytes_to_pixel_array([0x44u8, 0x33u8, 0x22u8, 0x11u8], 1) equals `[0x11223344u32]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: rejects empty, short, and overlong device buffers before indexing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Decode only one exact little-endian ARGB pixel")
expect(_bytes_to_pixel_array([], 0)).to_equal([])
expect(_bytes_to_pixel_array([], 1)).to_equal([])
expect(_bytes_to_pixel_array([0x44u8, 0x33u8, 0x22u8], 1)).to_equal([])
expect(_bytes_to_pixel_array([0x44u8, 0x33u8, 0x22u8, 0x11u8, 0x00u8], 1)).to_equal([])
expect(_bytes_to_pixel_array([0x44u8, 0x33u8, 0x22u8, 0x11u8], 1)).to_equal([0x11223344u32])
```

</details>

#### preserves the host cache and dirty state after a failed present readback

- Verify: preserves the host cache and dirty state after a failed present readback
   - Expected: b.completion_unknown is false
   - Expected: b.last_error equals `Vulkan framebuffer readback byte count mismatch`
   - Expected: b.dirty is true
   - Expected: b.host_buf equals `[0x11223344u32]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: preserves the host cache and dirty state after a failed present readback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 1
b.h = 1
b.d_framebuffer = 999999
b.dirty = true
b.host_buf = [0x11223344u32]
b.present()
expect(b.completion_unknown).to_equal(false)
expect(b.last_error).to_equal("Vulkan framebuffer readback byte count mismatch")
expect(b.dirty).to_equal(true)
expect(b.host_buf).to_equal([0x11223344u32])
```

</details>

#### accepts only bounded non-overlapping present damage

- Verify: accepts only bounded non-overlapping present damage
   - Expected: b.stage_present_damage([0, 0, 2, 2, 4, 1, 3, 4]) is true
   - Expected: b.present_damage_rects equals `[0, 0, 2, 2, 4, 1, 3, 4]`
   - Expected: b.stage_present_damage([0, 0, 4, 4, 3, 3, 2, 2]) is false
   - Expected: b.present_damage_valid is false
   - Expected: b.present_damage_rects equals `[]`
   - Expected: b.stage_present_damage([7, 5, 2, 1]) is false
   - Expected: b.stage_present_damage([0, 0, 1]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: accepts only bounded non-overlapping present damage")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 8
b.h = 6
expect(b.stage_present_damage([0, 0, 2, 2, 4, 1, 3, 4])).to_equal(true)
expect(b.present_damage_rects).to_equal([0, 0, 2, 2, 4, 1, 3, 4])
expect(b.stage_present_damage([0, 0, 4, 4, 3, 3, 2, 2])).to_equal(false)
expect(b.present_damage_valid).to_equal(false)
expect(b.present_damage_rects).to_equal([])
expect(b.stage_present_damage([7, 5, 2, 1])).to_equal(false)
expect(b.stage_present_damage([0, 0, 1])).to_equal(false)
```

</details>

#### does not partially commit the host mirror when damaged readback fails

- Verify: does not partially commit the host mirror when damaged readback fails
   - Expected: b.stage_present_damage([0, 0, 1, 1, 1, 1, 1, 1]) is true
   - Expected: b.dirty is true
   - Expected: b.host_buf equals `[1u32, 2u32, 3u32, 4u32]`
   - Expected: b.present_damage_valid is true
   - Expected: b.present_readback_bytes equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.present_attempted is false
   - Expected: receipt.present_completed is false
   - Expected: receipt.device_present is false
   - Expected: receipt.readback_requested is true
   - Expected: receipt.readback_completed is false
   - Expected: receipt.completion_known is true
   - Expected: receipt.fallback_reason equals `damaged-host-cache-refresh-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: does not partially commit the host mirror when damaged readback fails")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 2
b.h = 2
b.d_framebuffer = 999999
b.dirty = true
b.host_mirror_valid = true
b.host_buf = [1u32, 2u32, 3u32, 4u32]
expect(b.stage_present_damage([0, 0, 1, 1, 1, 1, 1, 1])).to_equal(true)
b.present()
expect(b.dirty).to_equal(true)
expect(b.host_buf).to_equal([1u32, 2u32, 3u32, 4u32])
expect(b.present_damage_valid).to_equal(true)
expect(b.present_readback_bytes).to_equal(0)  # oracle: pinned constant asserted by this scenario
val receipt = b.latest_frame_receipt()
expect(receipt.present_attempted).to_equal(false)
expect(receipt.present_completed).to_equal(false)
expect(receipt.device_present).to_equal(false)
expect(receipt.readback_requested).to_equal(true)
expect(receipt.readback_completed).to_equal(false)
expect(receipt.completion_known).to_equal(true)
expect(receipt.fallback_reason).to_equal("damaged-host-cache-refresh-failed")
```

</details>

#### finalizes a retained compute frame without host readback

- Verify: finalizes a retained compute frame without host readback
   - Expected: b.stage_present_damage([2, 1, 3, 2]) is true
   - Expected: b.finalize_compute_frame_no_readback() is true
   - Expected: b.dirty is true
   - Expected: b.host_mirror_valid is false
   - Expected: b.present_damage_valid is false
   - Expected: b.present_damage_rects equals `[]`
   - Expected: b.present_readback_bytes equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: b.present_readback_rect_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: b.device_finalize_no_readback_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.frame_index equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.framebuffer_width equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.framebuffer_height equals `6)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.dirty_rect_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.present_mode equals `device-retained`
   - Expected: receipt.present_attempted is false
   - Expected: receipt.present_completed is false
   - Expected: receipt.device_present is false
   - Expected: receipt.no_readback is true
   - Expected: receipt.readback_bytes equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.completion_known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: finalizes a retained compute frame without host readback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 8
b.h = 6
b.dirty = true
b.host_mirror_valid = true
b.host_buf = [0u32; 48]
expect(b.stage_present_damage([2, 1, 3, 2])).to_equal(true)
expect(b.finalize_compute_frame_no_readback()).to_equal(true)
expect(b.dirty).to_equal(true)
expect(b.host_mirror_valid).to_equal(false)
expect(b.present_damage_valid).to_equal(false)
expect(b.present_damage_rects).to_equal([])
expect(b.present_readback_bytes).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(b.present_readback_rect_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(b.device_finalize_no_readback_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
val receipt = b.latest_frame_receipt()
expect(receipt.frame_index).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(receipt.framebuffer_width).to_equal(8)  # oracle: pinned constant asserted by this scenario
expect(receipt.framebuffer_height).to_equal(6)  # oracle: pinned constant asserted by this scenario
expect(receipt.dirty_rect_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(receipt.present_mode).to_equal("device-retained")
expect(receipt.present_attempted).to_equal(false)
expect(receipt.present_completed).to_equal(false)
expect(receipt.device_present).to_equal(false)
expect(receipt.no_readback).to_equal(true)
expect(receipt.readback_bytes).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(receipt.completion_known).to_equal(true)
```

</details>

#### samples first damaged and last pixels inside the retained mirror owner

- Verify: samples first damaged and last pixels inside the retained mirror owner
   - Expected: b.sample_host_mirror([0, b.host_buf.len()]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: samples first damaged and last pixels inside the retained mirror owner")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 7680
b.h = 64
b.host_buf = [0u32; 7680 * 64]
val changed = 32 * 7680 + 320
var frame = 0
while frame < 210:
    b.host_buf[changed] = if frame % 2 == 0:
        0xffe62846u32
    else:
        0xff1ec86eu32
    frame += 1
expect(b.sample_host_mirror([0, changed, b.host_buf.len() - 1])).to_equal(
    [0u32, 0xff1ec86eu32, 0u32])
expect(b.sample_host_mirror([0, b.host_buf.len()])).to_equal([])
```

</details>

#### reports an idle host-cache call without inventing presentation

- Verify: reports an idle host-cache call without inventing presentation
   - Expected: receipt.frame_index equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.present_mode equals `none`
   - Expected: receipt.present_attempted is false
   - Expected: receipt.present_completed is false
   - Expected: receipt.device_present is false
   - Expected: receipt.readback_requested is false
   - Expected: receipt.readback_completed is false
   - Expected: receipt.no_readback is true
   - Expected: receipt.host_cache_refresh_completed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: reports an idle host-cache call without inventing presentation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 8
b.h = 6
b.present()
val receipt = b.latest_frame_receipt()
expect(receipt.frame_index).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(receipt.present_mode).to_equal("none")
expect(receipt.present_attempted).to_equal(false)
expect(receipt.present_completed).to_equal(false)
expect(receipt.device_present).to_equal(false)
expect(receipt.readback_requested).to_equal(false)
expect(receipt.readback_completed).to_equal(false)
expect(receipt.no_readback).to_equal(true)
expect(receipt.host_cache_refresh_completed).to_equal(false)
```

</details>

#### fails a missing headless swapchain without inventing device presentation

- Verify: fails a missing headless swapchain without inventing device presentation
   - Expected: b.present_headless_device() is false
   - Expected: receipt.present_mode equals `headless-swapchain`
   - Expected: receipt.present_attempted is true
   - Expected: receipt.present_completed is false
   - Expected: receipt.device_present is false
   - Expected: receipt.no_readback is true
   - Expected: receipt.swapchain_identity equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.fallback_reason equals `headless-swapchain-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: fails a missing headless swapchain without inventing device presentation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 8
b.h = 6
expect(b.present_headless_device()).to_equal(false)
val receipt = b.latest_frame_receipt()
expect(receipt.present_mode).to_equal("headless-swapchain")
expect(receipt.present_attempted).to_equal(true)
expect(receipt.present_completed).to_equal(false)
expect(receipt.device_present).to_equal(false)
expect(receipt.no_readback).to_equal(true)
expect(receipt.swapchain_identity).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(receipt.fallback_reason).to_equal("headless-swapchain-unavailable")
```

</details>

#### fails a missing window swapchain without inventing device presentation

- Verify: fails a missing window swapchain without inventing device presentation
   - Expected: b.present_window_device() is false
   - Expected: receipt.present_mode equals `window-swapchain`
   - Expected: receipt.present_attempted is true
   - Expected: receipt.present_completed is false
   - Expected: receipt.device_present is false
   - Expected: receipt.no_readback is true
   - Expected: receipt.swapchain_identity equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.fallback_reason equals `window-swapchain-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: fails a missing window swapchain without inventing device presentation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 8
b.h = 6
expect(b.present_window_device()).to_equal(false)
val receipt = b.latest_frame_receipt()
expect(receipt.present_mode).to_equal("window-swapchain")
expect(receipt.present_attempted).to_equal(true)
expect(receipt.present_completed).to_equal(false)
expect(receipt.device_present).to_equal(false)
expect(receipt.no_readback).to_equal(true)
expect(receipt.swapchain_identity).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(receipt.fallback_reason).to_equal("window-swapchain-unavailable")
```

</details>

#### preserves the host cache and dirty state after a failed image fallback readback

- Verify: preserves the host cache and dirty state after a failed image fallback readback
   - Expected: b.completion_unknown is false
   - Expected: b.cpu_fallback_used is false
   - Expected: b.last_error equals `Vulkan framebuffer readback byte count mismatch`
   - Expected: b.dirty is true
   - Expected: b.host_buf equals `[0x11223344u32]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: preserves the host cache and dirty state after a failed image fallback readback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 1
b.h = 1
b.d_framebuffer = 999999
b.dirty = true
b.host_buf = [0x11223344u32]
b.draw_image(0, 0, 1, 1, [0xFFFFFFFFu32])
expect(b.completion_unknown).to_equal(false)
expect(b.cpu_fallback_used).to_equal(false)
expect(b.last_error).to_equal("Vulkan framebuffer readback byte count mismatch")
expect(b.dirty).to_equal(true)
expect(b.host_buf).to_equal([0x11223344u32])
```

</details>

#### returns no device receipt after a failed dirty readback

- Verify: returns no device receipt after a failed dirty readback
   - Expected: readback.source equals `readback_failed`
   - Expected: readback.pixels equals `[]`
   - Expected: readback.backend_handle equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: readback.device_identity equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: b.dirty is true
   - Expected: b.host_buf equals `[0x11223344u32]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: returns no device receipt after a failed dirty readback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 1
b.h = 1
b.d_framebuffer = 999999
b.dirty = true
b.host_buf = [0x11223344u32]
val readback = b.read_pixels_with_source()
expect(readback.source).to_equal("readback_failed")
expect(readback.pixels).to_equal([])
expect(readback.backend_handle).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(readback.device_identity).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(b.dirty).to_equal(true)
expect(b.host_buf).to_equal([0x11223344u32])
```

</details>

#### 2D primitive rendering with lavapipe or real device

#### commits one damaged pixel after a full host-mirror seed

- Verify: commits one damaged pixel after a full host-mirror seed
   - Expected: b.host_mirror_valid is true
   - Expected: b.present_readback_bytes equals `48)  # oracle: pinned constant asserted by this scenario`
   - Expected: seed_receipt.present_mode equals `host-cache`
   - Expected: seed_receipt.present_completed is false
   - Expected: seed_receipt.device_present is false
   - Expected: seed_receipt.readback_completed is true
   - Expected: seed_receipt.host_cache_refresh_completed is true
   - Expected: seed_receipt.full_frame_fallback is true
   - Expected: seed_receipt.fallback_reason equals `host-mirror-seed`
   - Expected: b.stage_present_damage([2, 1, 1, 1]) is true
   - Expected: b.present_readback_bytes equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: b.present_readback_rect_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: damage_receipt.dirty_rect_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: damage_receipt.readback_bytes equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: damage_receipt.readback_completed is true
   - Expected: damage_receipt.full_frame_fallback is false
   - Expected: damage_receipt.present_completed is false
   - Expected: damage_receipt.device_present is false
   - Expected: b.host_buf equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: commits one damaged pixel after a full host-mirror seed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
if b.init(4, 3):
    val bg = 0xFF101010u32
    val changed = 0xFFABCDEFu32
    b.clear(bg)
    b.present()
    expect(b.host_mirror_valid).to_equal(true)
    expect(b.present_readback_bytes).to_equal(48)  # oracle: pinned constant asserted by this scenario
    val seed_receipt = b.latest_frame_receipt()
    expect(seed_receipt.present_mode).to_equal("host-cache")
    expect(seed_receipt.present_completed).to_equal(false)
    expect(seed_receipt.device_present).to_equal(false)
    expect(seed_receipt.readback_completed).to_equal(true)
    expect(seed_receipt.host_cache_refresh_completed).to_equal(true)
    expect(seed_receipt.full_frame_fallback).to_equal(true)
    expect(seed_receipt.fallback_reason).to_equal("host-mirror-seed")
    b.draw_rect_filled(2, 1, 1, 1, changed)
    expect(b.stage_present_damage([2, 1, 1, 1])).to_equal(true)
    b.present()
    expect(b.present_readback_bytes).to_equal(4)  # oracle: pinned constant asserted by this scenario
    expect(b.present_readback_rect_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
    val damage_receipt = b.latest_frame_receipt()
    expect(damage_receipt.dirty_rect_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
    expect(damage_receipt.readback_bytes).to_equal(4)  # oracle: pinned constant asserted by this scenario
    expect(damage_receipt.readback_completed).to_equal(true)
    expect(damage_receipt.full_frame_fallback).to_equal(false)
    expect(damage_receipt.present_completed).to_equal(false)
    expect(damage_receipt.device_present).to_equal(false)
    expect(b.host_buf).to_equal([
        bg, bg, bg, bg,
        bg, bg, changed, bg,
        bg, bg, bg, bg
    ])
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### commits two disjoint damaged regions from one packed refresh

- Verify: commits two disjoint damaged regions from one packed refresh
   - Expected: b.present_readback_bytes equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: b.present_readback_rect_count equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: b.host_buf equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: commits two disjoint damaged regions from one packed refresh")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
if b.init(4, 3):
    val bg = 0xFF101010u32
    val left = 0xFFAA1100u32
    val right = 0xFF00BB22u32
    b.clear(bg)
    b.present()
    b.draw_rect_filled(0, 0, 1, 1, left)
    b.draw_rect_filled(3, 2, 1, 1, right)
    expect(b.stage_present_damage([
        0, 0, 1, 1,
        3, 2, 1, 1,
    ])).to_equal(true)
    b.present()
    expect(b.present_readback_bytes).to_equal(8)  # oracle: pinned constant asserted by this scenario
    expect(b.present_readback_rect_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
    expect(b.host_buf).to_equal([
        left, bg, bg, bg,
        bg, bg, bg, bg,
        bg, bg, bg, right,
    ])
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### draws axis-aligned unit lines with inclusive endpoint parity

- Verify: draws axis-aligned unit lines with inclusive endpoint parity
   - Expected: pixels[1 * 5 + 1] equals `fg`
   - Expected: pixels[1 * 5 + 4] equals `fg`
   - Expected: pixels[2 * 5 + 3] equals `fg`
   - Expected: pixels[4 * 5 + 3] equals `fg`
   - Expected: pixels[0] equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: draws axis-aligned unit lines with inclusive endpoint parity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
if b.init(5, 5):
    val bg = 0xFF101010u32
    val fg = 0xFF22CC44u32
    b.clear(bg)
    b.draw_line(4, 1, 1, 1, fg, 1)
    b.draw_line(3, 4, 3, 2, fg, 1)
    val pixels = b.read_pixels()
    expect(pixels[1 * 5 + 1]).to_equal(fg)
    expect(pixels[1 * 5 + 4]).to_equal(fg)
    expect(pixels[2 * 5 + 3]).to_equal(fg)
    expect(pixels[4 * 5 + 3]).to_equal(fg)
    expect(pixels[0]).to_equal(bg)
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### scaled image clipping keeps device provenance and CPU-oracle pixels

- Verify: scaled image clipping keeps device provenance and CPU-oracle pixels
- Scale IMAGE pixels on the Vulkan device with CPU-oracle parity
   - Expected: readback.source equals `device_readback`
   - Expected: readback.pixels equals `[bg, red, green, bg]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: scaled image clipping keeps device provenance and CPU-oracle pixels")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
if b.init(4, 1):
    val bg = 0xFF000000u32
    val red = 0xFFFF0000u32
    val green = 0xFF00FF00u32
    b.clear(bg)
    b.set_clip(1, 0, 2, 1)
    step("Scale IMAGE pixels on the Vulkan device with CPU-oracle parity")
    b.draw_image_scaled(0, 0, 3, 1, 2, 1, [red, green])
    val readback = b.read_pixels_with_source()
    expect(readback.source).to_equal("device_readback")
    expect(readback.backend_handle).to_be_greater_than(0)
    expect(readback.device_identity).to_be_greater_than(0)
    expect(b.cpu_fallback_used).to_be(false)
    expect(readback.pixels).to_equal([bg, red, green, bg])
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### retains multiple image sources through one frame batch fence

- Verify: retains multiple image sources through one frame batch fence
   - Expected: b.pending_compute_count equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: b.pending_compute_sources[0] equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: readback.pixels equals `[red, bg, bg, green]`
   - Expected: readback.source equals `device_readback`
   - Expected: b.pending_compute_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: b.pending_compute_sources.len() equals `256)  # oracle: pinned constant asserted by this scenario`
   - Expected: source equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: retains multiple image sources through one frame batch fence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
if b.init(4, 1):
    val bg = 0xFF101010u32
    val red = 0xFFFF0000u32
    val green = 0xFF00FF00u32
    b.enable_frame_batching()
    b.clear(bg)
    b.draw_image(0, 0, 1, 1, [red])
    b.draw_image(3, 0, 1, 1, [green])
    expect(b.pending_compute_count).to_equal(3)  # oracle: pinned constant asserted by this scenario
    expect(b.pending_compute_sources[0]).to_equal(0)  # oracle: pinned constant asserted by this scenario
    expect(b.pending_compute_sources[1]).to_be_greater_than(0)
    expect(b.pending_compute_sources[2]).to_be_greater_than(0)
    val readback = b.read_pixels_with_source()
    expect(readback.pixels).to_equal([red, bg, bg, green])
    expect(readback.source).to_equal("device_readback")
    expect(b.pending_compute_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
    expect(b.pending_compute_sources.len()).to_equal(256)  # oracle: pinned constant asserted by this scenario
    for source in b.pending_compute_sources:
        expect(source).to_equal(0)  # oracle: pinned constant asserted by this scenario
    expect(b.cpu_fallback_used).to_be(false)
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### draw_line does not crash backend

- Verify: draw_line does not crash backend
   - Expected: pixels.len() equals `64)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: draw_line does not crash backend")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
if b.init(8, 8):
    val bg = 0x333333FFu32
    b.clear(bg)
    # draw_line(x1, y1, x2, y2, color, thickness)
    b.draw_line(0, 0, 7, 7, 0xFFFFFFFFu32, 1)
    b.present()
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(64)  # oracle: pinned constant asserted by this scenario
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### draw_circle does not crash backend

- Verify: draw_circle does not crash backend
   - Expected: pixels.len() equals `256)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: draw_circle does not crash backend")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
if b.init(16, 16):
    val bg = 0x444444FFu32
    b.clear(bg)
    # draw_circle(cx, cy, r, color)
    b.draw_circle(8, 8, 5, 0xFF8800FFu32)
    b.present()
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(256)  # oracle: pinned constant asserted by this scenario
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### draw_rect does not crash backend

- Verify: draw_rect does not crash backend
   - Expected: pixels.len() equals `64)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: draw_rect does not crash backend")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
if b.init(8, 8):
    val bg = 0x101010FFu32
    b.clear(bg)
    # draw_rect(x, y, w, h, color) — outline variant
    b.draw_rect(1, 1, 6, 6, 0xFFFFFFFFu32)
    b.present()
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(64)  # oracle: pinned constant asserted by this scenario
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### shutdown after init sets initialized to false

- Verify: shutdown after init sets initialized to false
   - Expected: b.width() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: b.height() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: shutdown after init sets initialized to false")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
if b.init(4, 4):
    b.shutdown()
    assert_false(b.initialized)
    expect(b.width()).to_equal(0)  # oracle: pinned constant asserted by this scenario
    expect(b.height()).to_equal(0)  # oracle: pinned constant asserted by this scenario
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### deterministic readback — lavapipe headless

#### clear to distinct color is deterministic across two inits

- Verify: clear to distinct color is deterministic across two inits
   - Expected: pixel_at_d(p1, 0, 0, 4) equals `pixel_at_d(p2, 0, 0, 4)`
   - Expected: pixel_at_d(p1, 3, 3, 4) equals `pixel_at_d(p2, 3, 3, 4)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: clear to distinct color is deterministic across two inits")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val color_a = 0xDEADBEFFu32
var b1 = VulkanBackend.create()
var b2 = VulkanBackend.create()
if b1.init(4, 4) and b2.init(4, 4):
    b1.clear(color_a)
    b1.present()
    b2.clear(color_a)
    b2.present()
    val p1 = b1.read_pixels()
    val p2 = b2.read_pixels()
    expect(pixel_at_d(p1, 0, 0, 4)).to_equal(pixel_at_d(p2, 0, 0, 4))
    expect(pixel_at_d(p1, 3, 3, 4)).to_equal(pixel_at_d(p2, 3, 3, 4))
    b1.shutdown()
    b2.shutdown()
else:
    # Neither device available — verify last_error is set
    if not b1.initialized:
        val kind = vulkan_classify_error(b1.last_error)
        assert_not_equal(kind, VulkanErrorKind.None)
    else:
        b1.shutdown()
```

</details>

### Vulkan 2D drawing lane — error path hardening

#### primitive dispatch provenance

#### fails closed for every primitive whose Vulkan pipeline is unavailable

- Verify: fails closed for every primitive whose Vulkan pipeline is unavailable
   - Expected: outline.cpu_fallback_reason equals `rect-outline-dispatch-failed`
   - Expected: circle.cpu_fallback_reason equals `circle-filled-dispatch-failed`
   - Expected: triangle.cpu_fallback_reason equals `triangle-filled-dispatch-failed`
   - Expected: gradient.cpu_fallback_reason equals `gradient-rect-dispatch-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: fails closed for every primitive whose Vulkan pipeline is unavailable")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var outline = VulkanBackend.create()
outline.w = 8
outline.h = 8
outline.draw_rect(1, 1, 4, 4, 0xFFFFFFFFu32)
expect(outline.cpu_fallback_used).to_be(true)
expect(outline.cpu_fallback_reason).to_equal("rect-outline-dispatch-failed")
expect(outline.dirty).to_be(false)
expect(outline.completion_unknown).to_be(false)

var circle = VulkanBackend.create()
circle.w = 8
circle.h = 8
circle.draw_circle_filled(4, 4, 2, 0xFFFFFFFFu32)
expect(circle.cpu_fallback_used).to_be(true)
expect(circle.cpu_fallback_reason).to_equal("circle-filled-dispatch-failed")

var triangle = VulkanBackend.create()
triangle.w = 8
triangle.h = 8
triangle.draw_triangle_filled(1, 1, 6, 1, 3, 6, 0xFFFFFFFFu32)
expect(triangle.cpu_fallback_used).to_be(true)
expect(triangle.cpu_fallback_reason).to_equal("triangle-filled-dispatch-failed")

var gradient = VulkanBackend.create()
gradient.w = 8
gradient.h = 8
gradient.draw_gradient_rect(1, 1, 4, 4, 0xFF000000u32, 0xFFFFFFFFu32)
expect(gradient.cpu_fallback_used).to_be(true)
expect(gradient.cpu_fallback_reason).to_equal("gradient-rect-dispatch-failed")
expect(gradient.dirty).to_be(false)
expect(gradient.completion_unknown).to_be(false)
```

</details>

#### routes clear and filled rectangle through the same checked provenance owner

- Verify: routes clear and filled rectangle through the same checked provenance owner
   - Expected: b.cpu_fallback_reason equals `clear-dispatch-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: routes clear and filled rectangle through the same checked provenance owner")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 8
b.h = 8
b.clear(0xFF000000u32)
b.draw_rect_filled(1, 1, 4, 4, 0xFFFFFFFFu32)
expect(b.cpu_fallback_used).to_be(true)
expect(b.cpu_fallback_reason).to_equal("clear-dispatch-failed")
expect(b.dirty).to_be(false)
expect(b.completion_unknown).to_be(false)
```

</details>

#### preserves the first primitive failure reason across later failures

- Verify: preserves the first primitive failure reason across later failures
   - Expected: b.cpu_fallback_reason equals `rect-outline-dispatch-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: preserves the first primitive failure reason across later failures")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.w = 8
b.h = 8
b.draw_rect(1, 1, 4, 4, 0xFFFFFFFFu32)
b.draw_circle_filled(4, 4, 2, 0xFFFFFFFFu32)
expect(b.cpu_fallback_reason).to_equal("rect-outline-dispatch-failed")
```

</details>

#### completion-unknown quarantine

#### preserves failed-idle state and makes successful release idempotent

- Verify: preserves failed-idle state and makes successful release idempotent
   - Expected: failed_idle.descriptor equals `11)  # oracle: pinned constant asserted by this scenario`
   - Expected: failed_idle.buffer equals `12)  # oracle: pinned constant asserted by this scenario`
   - Expected: vulkan_sffi_dependency_quarantine_empty(released) is true
   - Expected: vulkan_sffi_dependency_quarantine_empty(released_again) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: preserves failed-idle state and makes successful release idempotent")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val retained = VulkanSffiDependencyQuarantine(descriptor: 11, buffer: 12, pipeline: 13, shader: 14)
val failed_idle = vulkan_sffi_dependency_after_release(retained, false, true, true, true, true)
expect(failed_idle.descriptor).to_equal(11)  # oracle: pinned constant asserted by this scenario
expect(failed_idle.buffer).to_equal(12)  # oracle: pinned constant asserted by this scenario
val released = vulkan_sffi_dependency_after_release(retained, true, true, true, true, true)
expect(vulkan_sffi_dependency_quarantine_empty(released)).to_equal(true)
val released_again = vulkan_sffi_dependency_after_release(released, true, true, true, true, true)
expect(vulkan_sffi_dependency_quarantine_empty(released_again)).to_equal(true)
```

</details>

#### deduplicates already-owned typed handles

- Verify: deduplicates already-owned typed handles
   - Expected: vulkan_sffi_dependency_quarantine_empty(duplicate) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: deduplicates already-owned typed handles")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val retained = VulkanSffiDependencyQuarantine(descriptor: 21, buffer: 22, pipeline: 23, shader: 24)
val duplicate = vulkan_sffi_dependency_without_duplicates(retained, [retained])
expect(vulkan_sffi_dependency_quarantine_empty(duplicate)).to_equal(true)
```

</details>

#### freezes public drawing state until owner recovery

- Verify: freezes public drawing state until owner recovery
   - Expected: b.draw_image_blend_checked(0, 0, 1, 1, [0xFFFFFFFFu32], 1000) is false
   - Expected: b.dirty is true
   - Expected: b.host_buf equals `[0x11223344u32]`
   - Expected: b.clip_x equals `7)  # oracle: pinned constant asserted by this scenario`
   - Expected: readback.source equals `completion_unknown`
   - Expected: readback.pixels.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: readback.backend_handle equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: freezes public drawing state until owner recovery")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.initialized = true
b.completion_unknown = true
b.dirty = true
b.host_buf = [0x11223344u32]
b.clip_x = 7
b.clear(0xFFFFFFFFu32)
b.draw_rect(0, 0, 1, 1, 0xFFFFFFFFu32)
b.draw_image(0, 0, 1, 1, [0xFFFFFFFFu32])
expect(b.draw_image_blend_checked(0, 0, 1, 1, [0xFFFFFFFFu32], 1000)).to_equal(false)
b.present()
val readback = b.read_pixels_with_source()
expect(b.dirty).to_equal(true)
expect(b.host_buf).to_equal([0x11223344u32])
expect(b.clip_x).to_equal(7)  # oracle: pinned constant asserted by this scenario
expect(readback.source).to_equal("completion_unknown")
expect(readback.pixels.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(readback.backend_handle).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### structured error on missing device

#### init on host with no Vulkan sets classifiable last_error

- Verify: init on host with no Vulkan sets classifiable last_error


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: init on host with no Vulkan sets classifiable last_error")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
val ok = b.init(4, 4)
if not ok:
    val kind = vulkan_classify_error(b.last_error)
    # Error must be classified, never None
    assert_not_equal(kind, VulkanErrorKind.None)
    # Must be one of the expected failure categories
    val is_known = (kind == VulkanErrorKind.NotAvailable or
                    kind == VulkanErrorKind.NoDevice or
                    kind == VulkanErrorKind.ShaderCompile or
                    kind == VulkanErrorKind.DeviceLost or
                    kind == VulkanErrorKind.MissingExtension or
                    kind == VulkanErrorKind.Other)
    assert_true(is_known)
else:
    b.shutdown()
```

</details>

#### operations after failed init do not crash

- Verify: operations after failed init do not crash
   - Expected: pixels.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: operations after failed init do not crash")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
b.init(4, 4)
if not b.initialized:
    # These should not crash even with d_framebuffer == 0
    b.clear(0xFF000000u32)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
else:
    b.shutdown()
```

</details>

#### double shutdown is safe

- Verify: double shutdown is safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-006
step("Verify: double shutdown is safe")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = VulkanBackend.create()
if b.init(2, 2):
    b.shutdown()
    b.shutdown()
    assert_false(b.initialized)
else:
    # Even without init, shutdown should not crash
    b.shutdown()
    assert_false(b.initialized)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8651c973774d964d4cd17884daa6730901b0b14375381d7769e2571873abbd94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8651c973774d964d4cd17884daa6730901b0b14375381d7769e2571873abbd94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8651c973774d964d4cd17884daa6730901b0b14375381d7769e2571873abbd94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
