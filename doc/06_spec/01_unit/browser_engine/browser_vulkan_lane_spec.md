# Browser Vulkan Lane Specification

> Tests covering Browser Vulkan render lane.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Vulkan Lane Specification

## Scenarios

### Browser Vulkan render lane

#### reports honest backend provenance when vulkan is requested

- create a BrowserRenderer with the vulkan backend requested
- real vulkan backend initialized — no fallback reason expected
   - Expected: reason equals ``
- fallback path — must name software AND carry a concrete reason
   - Expected: name equals `software`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("create a BrowserRenderer with the vulkan backend requested")
val r = BrowserRenderer.create_with_backend(W, H, "vulkan")
val name = r.backend_name()
val reason = r.backend_fallback_reason()
if name.contains("vulkan"):
    step("real vulkan backend initialized — no fallback reason expected")
    expect(reason).to_equal("")
else:
    step("fallback path — must name software AND carry a concrete reason")
    expect(name).to_equal("software")
    expect(reason.len()).to_be_greater_than(0)
```

</details>

#### never labels the vulkan lane frame as vulkan unless device readback ran

- render a small two-tone page through the vulkan lane
   - Expected: frame.reason equals ``
   - Expected: frame.backend equals `software`
- the frame carries a full viewport of pixels either way
   - Expected: frame.pixels.len() equals `W * H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("render a small two-tone page through the vulkan lane")
val frame = browser_render_html_vulkan(HTML, W, H)
if frame.backend == "vulkan":
    expect(frame.reason).to_equal("")
else:
    expect(frame.backend).to_equal("software")
    expect(frame.reason.len()).to_be_greater_than(0)
step("the frame carries a full viewport of pixels either way")
expect(frame.pixels.len()).to_equal(W * H)
```

</details>

#### selects the vulkan lane via SIMPLE_BROWSER_RENDER_LANE

- set SIMPLE_BROWSER_RENDER_LANE=vulkan
   - Expected: browser_render_lane_is_known(BROWSER_RENDER_LANE_VULKAN) is true
   - Expected: browser_render_lane_selected() equals `BROWSER_RENDER_LANE_VULKAN`
- restore the default lane selection
   - Expected: browser_render_lane_selected() equals `BROWSER_RENDER_LANE_LIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("set SIMPLE_BROWSER_RENDER_LANE=vulkan")
env_set(BROWSER_RENDER_LANE_ENV, BROWSER_RENDER_LANE_VULKAN)
expect(browser_render_lane_is_known(BROWSER_RENDER_LANE_VULKAN)).to_equal(true)
expect(browser_render_lane_selected()).to_equal(BROWSER_RENDER_LANE_VULKAN)
step("restore the default lane selection")
env_set(BROWSER_RENDER_LANE_ENV, "")
expect(browser_render_lane_selected()).to_equal(BROWSER_RENDER_LANE_LIVE)
```

</details>

#### produces non-empty pixels for a small viewport through the vulkan lane

- dispatch through render_html_to_pixel_array_via('vulkan')
   - Expected: pixels.len() equals `W * H`
- count non-zero pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("dispatch through render_html_to_pixel_array_via('vulkan')")
val pixels = render_html_to_pixel_array_via(BROWSER_RENDER_LANE_VULKAN, HTML, W, H)
expect(pixels.len()).to_equal(W * H)
step("count non-zero pixels")
var nonzero = 0
var i = 0
while i < pixels.len():
    if (pixels[i] & 0xFFFFFFu32) != 0u32:
        nonzero = nonzero + 1
    i = i + 1
expect(nonzero).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/browser_vulkan_lane_spec.spl` |
| Updated | 2026-08-15 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser Vulkan render lane.
- Browser Vulkan render lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
