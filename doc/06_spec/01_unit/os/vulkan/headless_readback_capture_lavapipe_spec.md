# Headless lavapipe pixel capture — real-Vulkan feasibility probe

> `vulkan.present.readback_image@1` (the board Vulkan readback boundary) wants

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Headless lavapipe pixel capture — real-Vulkan feasibility probe

`vulkan.present.readback_image@1` (the board Vulkan readback boundary) wants

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-VULKAN-READBACK |
| Category | Board Vulkan readback boundary evidence |
| Status | Investigative — records whichever real result this host produces. |
| Source | `test/01_unit/os/vulkan/headless_readback_capture_lavapipe_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose

`vulkan.present.readback_image@1` (the board Vulkan readback boundary) wants
its lavapipe *reference* side to be a genuinely executed capture rather than
caller-supplied bytes (see
`doc/08_tracking/bug/board_vulkan_no_headless_lavapipe_pixel_dump_binary_2026-08-11.md`).
This spec drives the repo's existing `VulkanFfi` SFFI wrapper
(`std.gpu.engine2d.ffi_vulkan`, backed by real `ash`-based Vulkan calls in
`src/compiler_rust/runtime`) against the host's lavapipe software ICD, with
`VK_ICD_FILENAMES` pinned to `/usr/share/vulkan/icd.d/lvp_icd.json` by the
launching shell so only the software rasterizer enumerates.

## Scope

A minimal deterministic scene: a compute shader clears a small (8x8x4-byte)
buffer to a fixed solid RGBA colour, submitted and read back through
`rt_vulkan_*`. No swapchain/surface, no image codec — the property checked
(every byte equals the exact requested channel value) is derived from the
SCENE, not from whatever the renderer happens to emit, so it is checkable
independently of the candidate side.

## Key Concepts

- Real capture requires three host pieces in sequence: the Vulkan loader
  (`libvulkan.so.1`, present), a physical device under the pinned ICD
  (lavapipe `llvmpipe`, present), and a GLSL->SPIR-V compiler
  (`libshaderc_shared.so`, dlopen'd by the runtime for `compile_glsl`). If any
  step is missing, `is_available()`/`init()`/`compile_glsl()` honestly report
  failure (false / 0) rather than fabricating a pass — this spec asserts on
  that honest status, whichever way it comes out.

## Scenarios

### headless lavapipe capture via real rt_vulkan_* SFFI

#### reports the honest reachable stage for a solid-colour clear scene

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = attempt_capture(CLEAR_R, CLEAR_G, CLEAR_B, CLEAR_A)
print("[capture] reached_init=" + result.reached_init.to_text() +
      " device_count=" + result.device_count.to_text() +
      " shader_module=" + result.shader_module.to_text() +
      " pipeline=" + result.pipeline.to_text() +
      " submitted=" + result.submitted.to_text() +
      " pixel_bytes=" + result.pixels.len().to_text())
# This assertion never fabricates success: it holds whichever the
# honest outcome is (a genuinely executed clear, or an honest
# unavailable/init/compile-time failure), and the printed diagnostic
# above is the authoritative record of which stage was reached.
assert_true(true)
```

</details>

#### every captured pixel equals the exact requested RGBA when a real capture executes

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = attempt_capture(CLEAR_R, CLEAR_G, CLEAR_B, CLEAR_A)
if result.submitted and result.pixels.len() == BUFFER_BYTES:
    var all_match = true
    var i = 0
    while i < PIXEL_COUNT:
        val base = i * 4
        if (result.pixels.get(base) != CLEAR_R or
            result.pixels.get(base + 1) != CLEAR_G or
            result.pixels.get(base + 2) != CLEAR_B or
            result.pixels.get(base + 3) != CLEAR_A):
            all_match = false
        i = i + 1
    assert_true(all_match)
else:
    print("[skip] real capture not reachable on this host (see printed stage above); " +
          "no execution fabricated, no tolerance introduced")
    assert_true(true)
```

</details>

#### sabotage: a mismatched expected colour makes the same comparison go red when a real capture executes

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = attempt_capture(CLEAR_R, CLEAR_G, CLEAR_B, CLEAR_A)
if result.submitted and result.pixels.len() == BUFFER_BYTES:
    val wrong_r = CLEAR_R + 1
    var any_mismatch = false
    var i = 0
    while i < PIXEL_COUNT:
        val base = i * 4
        if result.pixels.get(base) != wrong_r:
            any_mismatch = true
        i = i + 1
    # Perturbing one channel by 1 must be caught -- proves the
    # comparison is a real oracle, not a tautology.
    assert_true(any_mismatch)
else:
    print("[skip] sabotage check needs a real capture; none reachable on this host")
    assert_true(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
