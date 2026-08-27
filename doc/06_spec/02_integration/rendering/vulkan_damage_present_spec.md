# vulkan_damage_present_spec

> Live Vulkan damaged host-mirror synchronization parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_damage_present_spec

Live Vulkan damaged host-mirror synchronization parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/vulkan_damage_present_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

Live Vulkan damaged host-mirror synchronization parity.

Purpose: prove that the production Vulkan backend synchronizes exact retained
damage instead of reading the full framebuffer after every local update.
Audience: rendering maintainers validating Vulkan transfer performance and
pixel correctness. Scope: host-cache synchronization only; this is not
swapchain presentation or 8K/80 performance evidence.
Precondition: a Vulkan implementation is available; CI uses pinned lavapipe.
Verification: require exact transfer receipts and whole-buffer pixel parity.
Recovery: an unavailable device must expose a non-empty initialization error;
a transfer mismatch must preserve dirty state and invalidate the host mirror.

REQ-VKD-001: a seeded mirror transfers only exact local damage bytes.
REQ-VKD-002: an idle retained frame performs no transfer.
REQ-VKD-003: an unseeded mirror fails closed to one full refresh.

## Scenarios

### Vulkan damaged present

#### retained host mirror

#### REQ-VKD-001 seeds once then transfers only an exact local rectangle

- Seed the retained host mirror from a completed Vulkan frame
   - Expected: backend.host_mirror_valid is true
- Refresh only the exact three-by-two damaged rectangle
   - Expected: transferred is true
   - Expected: backend.damage_readback_calls equals `1`
   - Expected: backend.damage_readback_rects equals `1`
   - Expected: backend.damage_readback_bytes equals `24`
   - Expected: backend.damage_full_fallbacks equals `0`
- Compare the entire retained mirror, including outside sentinels
   - Expected: mismatches equals `0`
   - Expected: backend.last_error == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanBackend.create()
val initialized = backend.init(8, 4)
if initialized:
    step("Seed the retained host mirror from a completed Vulkan frame")
    val background = rgb(8, 16, 24)
    val foreground = rgb(240, 80, 32)
    backend.clear(background)
    backend.present()
    expect(backend.host_mirror_valid).to_equal(true)
    backend.draw_rect_filled(2, 1, 3, 2, foreground)
    step("Refresh only the exact three-by-two damaged rectangle")
    val transferred = backend.present_damage_plan(
        local_plan([2, 1, 3, 2], 6))
    expect(transferred).to_equal(true)
    expect(backend.damage_readback_calls).to_equal(1)
    expect(backend.damage_readback_rects).to_equal(1)
    expect(backend.damage_readback_bytes).to_equal(24)
    expect(backend.damage_full_fallbacks).to_equal(0)
    step("Compare the entire retained mirror, including outside sentinels")
    var mismatches = 0
    var y = 0
    while y < 4:
        var x = 0
        while x < 8:
            val expected = if x >= 2 and x < 5 and y >= 1 and y < 3: foreground else: background
            if backend.host_buf[y * 8 + x] != expected:
                mismatches = mismatches + 1
            x = x + 1
        y = y + 1
    expect(mismatches).to_equal(0)
    backend.shutdown()
else:
    expect(backend.last_error == "").to_equal(false)
```

</details>

#### REQ-VKD-002 does no transfer for an idle clean frame

- Submit an empty plan after the frame is already clean
   - Expected: backend.present_damage_plan(none_plan()) is true
   - Expected: backend.damage_readback_calls equals `calls_before`
   - Expected: backend.damage_readback_bytes equals `bytes_before`
   - Expected: backend.last_error == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanBackend.create()
val initialized = backend.init(4, 4)
if initialized:
    backend.clear(rgb(1, 2, 3))
    backend.present()
    step("Submit an empty plan after the frame is already clean")
    val calls_before = backend.damage_readback_calls
    val bytes_before = backend.damage_readback_bytes
    expect(backend.present_damage_plan(none_plan())).to_equal(true)
    expect(backend.damage_readback_calls).to_equal(calls_before)
    expect(backend.damage_readback_bytes).to_equal(bytes_before)
    backend.shutdown()
else:
    expect(backend.last_error == "").to_equal(false)
```

</details>

#### REQ-VKD-003 falls back to one full refresh when the mirror is not seeded

- Offer local damage before any full mirror seed exists
   - Expected: backend.host_mirror_valid is false
   - Expected: backend.host_mirror_valid is true
   - Expected: backend.damage_full_fallbacks equals `1`
   - Expected: backend.damage_readback_calls equals `0`
   - Expected: backend.host_buf[5] equals `foreground`
   - Expected: backend.host_buf[10] equals `foreground`
   - Expected: backend.last_error == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanBackend.create()
val initialized = backend.init(4, 4)
if initialized:
    val foreground = rgb(90, 100, 110)
    backend.clear(rgb(0, 0, 0))
    backend.draw_rect_filled(1, 1, 2, 2, foreground)
    step("Offer local damage before any full mirror seed exists")
    expect(backend.host_mirror_valid).to_equal(false)
    expect(backend.present_damage_plan(
        local_plan([1, 1, 2, 2], 4))).to_equal(true)
    expect(backend.host_mirror_valid).to_equal(true)
    expect(backend.damage_full_fallbacks).to_equal(1)
    expect(backend.damage_readback_calls).to_equal(0)
    expect(backend.host_buf[5]).to_equal(foreground)
    expect(backend.host_buf[10]).to_equal(foreground)
    backend.shutdown()
else:
    expect(backend.last_error == "").to_equal(false)
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
