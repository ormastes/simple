# Web-Render Engine2D Surface

> The second API surface (web-render) composites a web page scene through the real Engine2D backends — Vulkan, Metal-on-Vulkan, DirectX-on-Vulkan — with HONEST provenance. The scene is rendered through `Engine2D.create_requested_backend`, so the pixels genuinely come from the named backend and the reported backend name is the one that actually rendered (not a fabricated label like the legacy web pixel path). Each GPU backend must match the `SoftwareBackend` reference pixel-for-pixel WHEN it genuinely rendered through that backend; otherwise it must report a name that does NOT claim the backend (truthful fallback). No false-greening either way.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web-Render Engine2D Surface

The second API surface (web-render) composites a web page scene through the real Engine2D backends — Vulkan, Metal-on-Vulkan, DirectX-on-Vulkan — with HONEST provenance. The scene is rendered through `Engine2D.create_requested_backend`, so the pixels genuinely come from the named backend and the reported backend name is the one that actually rendered (not a fabricated label like the legacy web pixel path). Each GPU backend must match the `SoftwareBackend` reference pixel-for-pixel WHEN it genuinely rendered through that backend; otherwise it must report a name that does NOT claim the backend (truthful fallback). No false-greening either way.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Implemented |
| Requirements | N/A |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The second API surface (web-render) composites a web page scene through the real
Engine2D backends — Vulkan, Metal-on-Vulkan, DirectX-on-Vulkan — with HONEST
provenance. The scene is rendered through `Engine2D.create_requested_backend`, so
the pixels genuinely come from the named backend and the reported backend name is
the one that actually rendered (not a fabricated label like the legacy web pixel
path). Each GPU backend must match the `SoftwareBackend` reference pixel-for-pixel
WHEN it genuinely rendered through that backend; otherwise it must report a name
that does NOT claim the backend (truthful fallback). No false-greening either way.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Vulkan device prime | A direct `VulkanBackend` `it` runs first so the SSpec runner resolves the real device for the later Engine2D-routed steps |
| Inline render | The Engine2D create+draw must stay inline in each `it` (a helper fn or wrapper module makes the runner fall back to CPU) |
| Opaque page background | The background is composited opaquely — a deterministic copy on every backend, sidestepping the non-opaque blend-vs-copy divergence |
| Reference oracle | A direct `SoftwareBackend.create()` rendering of the same scene — never the GPU compared to itself |

## Related Specifications

- [Vulkan Compute Oracle](../engine2d/vulkan_compute_oracle_spec.md) — the same three backends verified directly on the Engine2D API

## Scenarios

### Web-render surface composited through Engine2D backends

#### software reference composites the page background into a uniform opaque surface

- primes the real Vulkan device for the Engine2D-routed web render
- Create a direct VulkanBackend (primes rt_vulkan_* for the runner)
- If real Vulkan is unavailable, assert the device count is honestly zero
   - Expected: rt_vulkan_device_count() equals `0`
- A direct clear+readback returns the exact clear color
   - Expected: px.len() equals `32 * 32`
   - Expected: px[0] equals `0xFF112233u32`
- software reference composites the page background into a uniform opaque surface
- Composite the web scene through the SoftwareBackend reference
   - Expected: px.len() equals `48 * 32`
- Every pixel is the same fully-opaque color (a uniform page background)


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("primes the real Vulkan device for the Engine2D-routed web render")
step("Create a direct VulkanBackend (primes rt_vulkan_* for the runner)")
var vb = VulkanBackend.create()
val ok = vb.init(32, 32)

step("If real Vulkan is unavailable, assert the device count is honestly zero")
if not ok:
    expect(rt_vulkan_device_count()).to_equal(0)
    return

step("A direct clear+readback returns the exact clear color")
vb.clear(0xFF112233u32)
val px = vb.read_pixels()
expect(px.len()).to_equal(32 * 32)
expect(px[0]).to_equal(0xFF112233u32)

# @req REQ-SSPEC-LIB
step("software reference composites the page background into a uniform opaque surface")
step("Composite the web scene through the SoftwareBackend reference")
val px = software_web_scene()
expect(px.len()).to_equal(48 * 32)

step("Every pixel is the same fully-opaque color (a uniform page background)")
val first = px[0]
var uniform = true
var alpha_ok = true
var i = 0
while i < px.len():
    if px[i] != first:
        uniform = false
    if (px[i] / 16777216) % 256 != 255:
        alpha_ok = false
    i = i + 1
expect(uniform).to_be(true)
expect(alpha_ok).to_be(true)
```

</details>

#### Vulkan-backed web render matches the software reference

- primes the real Vulkan device for the Engine2D-routed web render
- Create a direct VulkanBackend (primes rt_vulkan_* for the runner)
- If real Vulkan is unavailable, assert the device count is honestly zero
   - Expected: rt_vulkan_device_count() equals `0`
- A direct clear+readback returns the exact clear color
   - Expected: px.len() equals `32 * 32`
   - Expected: px[0] equals `0xFF112233u32`
- Vulkan-backed web render matches the software reference
- Render the page scene inline through the Vulkan backend, compare to the SoftwareBackend reference
- When genuinely Vulkan, pixels match the reference; otherwise the name does not claim Vulkan


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("primes the real Vulkan device for the Engine2D-routed web render")
step("Create a direct VulkanBackend (primes rt_vulkan_* for the runner)")
var vb = VulkanBackend.create()
val ok = vb.init(32, 32)

step("If real Vulkan is unavailable, assert the device count is honestly zero")
if not ok:
    expect(rt_vulkan_device_count()).to_equal(0)
    return

step("A direct clear+readback returns the exact clear color")
vb.clear(0xFF112233u32)
val px = vb.read_pixels()
expect(px.len()).to_equal(32 * 32)
expect(px[0]).to_equal(0xFF112233u32)

# @req REQ-SSPEC-LIB
step("Vulkan-backed web render matches the software reference")
step("Render the page scene inline through the Vulkan backend, compare to the SoftwareBackend reference")
val sw = software_web_scene()
val scene = simple_web_render_html_to_scene(HTML, 48, 32)
var r = Engine2D.create_requested_backend(48, 32, "vulkan")
var eng = r.unwrap()
val name = eng.backend_name()
eng.clear(0xFFFFFFFFu32)
var i = 0
while i < scene.commands.len():
    if scene.commands[i].kind == "fill_rect":
        eng.draw_rect_filled(0, 0, 48, 32, scene.commands[i].color | 0xFF000000u32)
    i = i + 1
val px = eng.read_pixels()
step("When genuinely Vulkan, pixels match the reference; otherwise the name does not claim Vulkan")
val ok = if name == "vulkan": pixel_mismatches(px, sw) == 0 and px.len() == 48 * 32 else: name != "vulkan"
expect(ok).to_be(true)
```

</details>

#### Metal-on-Vulkan web render matches the software reference

- primes the real Vulkan device for the Engine2D-routed web render
- Create a direct VulkanBackend (primes rt_vulkan_* for the runner)
- If real Vulkan is unavailable, assert the device count is honestly zero
   - Expected: rt_vulkan_device_count() equals `0`
- A direct clear+readback returns the exact clear color
   - Expected: px.len() equals `32 * 32`
   - Expected: px[0] equals `0xFF112233u32`
- Metal-on-Vulkan web render matches the software reference
- Render the page scene inline through the Metal-on-Vulkan backend, compare to the reference
- When genuinely metal-on-vulkan, pixels match the reference; otherwise the name does not claim it


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("primes the real Vulkan device for the Engine2D-routed web render")
step("Create a direct VulkanBackend (primes rt_vulkan_* for the runner)")
var vb = VulkanBackend.create()
val ok = vb.init(32, 32)

step("If real Vulkan is unavailable, assert the device count is honestly zero")
if not ok:
    expect(rt_vulkan_device_count()).to_equal(0)
    return

step("A direct clear+readback returns the exact clear color")
vb.clear(0xFF112233u32)
val px = vb.read_pixels()
expect(px.len()).to_equal(32 * 32)
expect(px[0]).to_equal(0xFF112233u32)

# @req REQ-SSPEC-LIB
step("Metal-on-Vulkan web render matches the software reference")
step("Render the page scene inline through the Metal-on-Vulkan backend, compare to the reference")
val sw = software_web_scene()
val scene = simple_web_render_html_to_scene(HTML, 48, 32)
var r = Engine2D.create_requested_backend(48, 32, "metal-on-vulkan")
var eng = r.unwrap()
val name = eng.backend_name()
eng.clear(0xFFFFFFFFu32)
var i = 0
while i < scene.commands.len():
    if scene.commands[i].kind == "fill_rect":
        eng.draw_rect_filled(0, 0, 48, 32, scene.commands[i].color | 0xFF000000u32)
    i = i + 1
val px = eng.read_pixels()
step("When genuinely metal-on-vulkan, pixels match the reference; otherwise the name does not claim it")
val ok = if name == "metal-on-vulkan": pixel_mismatches(px, sw) == 0 and px.len() == 48 * 32 else: name != "metal-on-vulkan"
expect(ok).to_be(true)
```

</details>

#### DirectX-on-Vulkan web render matches the software reference

- primes the real Vulkan device for the Engine2D-routed web render
- Create a direct VulkanBackend (primes rt_vulkan_* for the runner)
- If real Vulkan is unavailable, assert the device count is honestly zero
   - Expected: rt_vulkan_device_count() equals `0`
- A direct clear+readback returns the exact clear color
   - Expected: px.len() equals `32 * 32`
   - Expected: px[0] equals `0xFF112233u32`
- DirectX-on-Vulkan web render matches the software reference
- Render the page scene inline through the DirectX-on-Vulkan backend, compare to the reference
- When genuinely directx-on-vulkan, pixels match the reference; otherwise the name does not claim it


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("primes the real Vulkan device for the Engine2D-routed web render")
step("Create a direct VulkanBackend (primes rt_vulkan_* for the runner)")
var vb = VulkanBackend.create()
val ok = vb.init(32, 32)

step("If real Vulkan is unavailable, assert the device count is honestly zero")
if not ok:
    expect(rt_vulkan_device_count()).to_equal(0)
    return

step("A direct clear+readback returns the exact clear color")
vb.clear(0xFF112233u32)
val px = vb.read_pixels()
expect(px.len()).to_equal(32 * 32)
expect(px[0]).to_equal(0xFF112233u32)

# @req REQ-SSPEC-LIB
step("DirectX-on-Vulkan web render matches the software reference")
step("Render the page scene inline through the DirectX-on-Vulkan backend, compare to the reference")
val sw = software_web_scene()
val scene = simple_web_render_html_to_scene(HTML, 48, 32)
var r = Engine2D.create_requested_backend(48, 32, "directx-on-vulkan")
var eng = r.unwrap()
val name = eng.backend_name()
eng.clear(0xFFFFFFFFu32)
var i = 0
while i < scene.commands.len():
    if scene.commands[i].kind == "fill_rect":
        eng.draw_rect_filled(0, 0, 48, 32, scene.commands[i].color | 0xFF000000u32)
    i = i + 1
val px = eng.read_pixels()
step("When genuinely directx-on-vulkan, pixels match the reference; otherwise the name does not claim it")
val ok = if name == "directx-on-vulkan": pixel_mismatches(px, sw) == 0 and px.len() == 48 * 32 else: name != "directx-on-vulkan"
expect(ok).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `35bffb4969418ae46b7506755d0b8de61e6a9aadc7c4305df0fe3fc65bc86d20`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35bffb4969418ae46b7506755d0b8de61e6a9aadc7c4305df0fe3fc65bc86d20`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35bffb4969418ae46b7506755d0b8de61e6a9aadc7c4305df0fe3fc65bc86d20`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'primes the real Vulkan device for the Engine2D-routed web render' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'software reference composites the page background into a uniform opaque surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Vulkan-backed web render matches the software reference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
