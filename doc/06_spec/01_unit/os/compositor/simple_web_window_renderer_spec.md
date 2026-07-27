# Simple Web Window Renderer Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Window Renderer Specification

## Scenarios

### Simple Web compositor adapter

#### accepts only exact solid, CPU, and Metal material provenance reasons

<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sha256 = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
val solid = _web_provenance_frame(
    "solid-material",
    "cpu-raster-backdrop-sampling-unavailable",
    sha256,
    sha256
)
val cpu = _web_provenance_frame(
    "cpu-composited-material",
    "native-device-backdrop-path-pending",
    sha256,
    sha256
)
val metal = _web_provenance_frame(
    "metal-device-composited-material",
    "metal-device-glass-dispatch",
    sha256,
    sha256
)
val wrong_solid = _web_provenance_frame(
    "solid-material",
    "some-other-reason",
    sha256,
    sha256
)
val wrong_cpu = _web_provenance_frame(
    "cpu-composited-material",
    "cpu-raster-backdrop-sampling-unavailable",
    sha256,
    sha256
)
val wrong_metal = _web_provenance_frame(
    "metal-device-composited-material",
    "native-device-backdrop-path-pending",
    sha256,
    sha256
)
expect(wm_content_frame_web_provenance_valid(solid)).to_be(true)
expect(wm_content_frame_web_provenance_valid(cpu)).to_be(true)
expect(wm_content_frame_web_provenance_valid(metal)).to_be(true)
expect(wm_content_frame_web_provenance_valid(wrong_solid)).to_be(false)
expect(wm_content_frame_web_provenance_valid(wrong_cpu)).to_be(false)
expect(wm_content_frame_web_provenance_valid(wrong_metal)).to_be(false)
```

</details>

#### rejects non-lowercase or nonhex material and manifest SHA-256 receipts

<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_sha256 = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
val uppercase_sha256 = "0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF"
val nonhex_sha256 = "g123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
val uppercase_material = _web_provenance_frame(
    "cpu-composited-material",
    "native-device-backdrop-path-pending",
    uppercase_sha256,
    valid_sha256
)
val nonhex_material = _web_provenance_frame(
    "cpu-composited-material",
    "native-device-backdrop-path-pending",
    nonhex_sha256,
    valid_sha256
)
val uppercase_manifest = _web_provenance_frame(
    "cpu-composited-material",
    "native-device-backdrop-path-pending",
    valid_sha256,
    uppercase_sha256
)
val nonhex_manifest = _web_provenance_frame(
    "cpu-composited-material",
    "native-device-backdrop-path-pending",
    valid_sha256,
    nonhex_sha256
)
expect(wm_content_frame_web_provenance_valid(uppercase_material)).to_be(false)
expect(wm_content_frame_web_provenance_valid(nonhex_material)).to_be(false)
expect(wm_content_frame_web_provenance_valid(uppercase_manifest)).to_be(false)
expect(wm_content_frame_web_provenance_valid(nonhex_manifest)).to_be(false)
```

</details>

#### uses the canonical Web Draw IR and Engine2D backend by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = file_read("src/os/compositor/simple_web_window_renderer.spl")
val host = file_read("src/os/compositor/host_compositor_core.spl")
val surface = file_read("src/os/compositor/web_render_surface.spl")
expect(renderer).to_contain("std.gc_async_mut.ui.web_render_pixel_backend")
expect(host).to_contain("std.gc_async_mut.ui.web_render_pixel_backend")
expect(surface).to_contain("std.gc_async_mut.ui.web_render_pixel_backend")
expect(surface).to_contain("web_render_request_to_pixel_artifact(req)")
expect(renderer.contains("web_render_pixel_software_backend")).to_be(false)
expect(host.contains("web_render_pixel_software_backend")).to_be(false)
expect(surface.contains("web_render_request_to_native_safe_pixel_artifact")).to_be(false)
```

</details>

#### produces an authoritative shared-WM frame from runtime HTML

- assert not equal
   - Expected: frame.material_fallback_kind equals `cpu-composited-material`
   - Expected: frame.material_fallback_reason equals `native-device-backdrop-path-pending`
   - Expected: frame.material_fallback_sha256.len() equals `64`
   - Expected: frame.theme_id equals `glass_dark`
   - Expected: frame.theme_source_manifest_sha256.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = web_render_pixel_artifact_cache(36, 18, "software")
val body = "<p data-runtime='yes'>runtime-created content</p>"
val frame = simple_web_content_frame_cached(cache, "window-42", 9, 4, "glass_dark", "Arbitrary runtime title", body, 36, 18, 0)
expect(frame.window_id).to_equal("window-42")
expect(frame.scene_revision).to_equal(9)
expect(frame.content_revision).to_equal(4)
expect(frame.origin_kind).to_equal(WM_CONTENT_ORIGIN_SIMPLE_WEB)
expect(frame.width).to_equal(36)
expect(frame.height).to_equal(18)
expect(frame.pixels.len()).to_equal(36 * 18)
expect(frame.checksum).to_be_greater_than(0u64)
expect(frame.engine2d_status).to_equal("engine2d_rendered")
expect(frame.engine2d_backend.len()).to_be_greater_than(0)
assert_not_equal(frame.engine2d_backend, "native-safe-fallback")
expect(frame.material_fallback_kind).to_equal("cpu-composited-material")
expect(frame.material_fallback_reason).to_equal("native-device-backdrop-path-pending")
expect(frame.material_fallback_sha256.len()).to_equal(64)
expect(frame.theme_id).to_equal("glass_dark")
expect(frame.theme_source_manifest_sha256.len()).to_equal(64)
expect(wm_content_frame_web_provenance_valid(frame)).to_be(true)
```

</details>

#### turns validated external DrawIR execution into a web frame

- raster shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = simple_web_content_full_html_with_theme(
    "glass_dark", "External", "<p>worker-owned</p>", 64, 48
)
val layout = simple_web_layout_render_html_draw_ir_result(html, 64, 48)
val raster = Engine2dCompositorBackend.create_named(
    64, 48, "software"
)
val render = raster.render_draw_ir_composition(
    layout.composition, []
)
val frame = simple_web_external_content_frame(
    "external",
    7,
    "glass_dark",
    64,
    48,
    render,
    layout.material_witness.cpu_composited_count,
    layout.material_witness.cpu_composited_sha256,
    layout.material_witness.solid_material_count,
    layout.material_witness.solid_material_sha256
)
expect(frame.pixels.len()).to_equal(64 * 48)
expect(frame.checksum).to_be_greater_than(0u64)
expect(wm_content_frame_web_provenance_valid(frame)).to_be(true)
raster.shutdown()
```

</details>

#### renders bounded CSS animation frames then becomes quiescent

- assert not equal
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "<style>@keyframes pulse { from { background-color:#ef4444; } to { background-color:#2563eb; } } #stage { width:32px; height:24px; animation:pulse 1000ms linear forwards; }</style><div id='stage'></div>"
val revision = simple_web_content_revision_with_theme(
    "glass_dark", "Animation", body, 64, 48, 0
)
val cache = web_render_pixel_artifact_cache(64, 48, "software")
val first = simple_web_content_frame_cached_at_time(
    cache, "animated", 1, revision, "glass_dark", "Animation",
    body, 64, 48, 0, 1000
)
expect(contains_pixel(first.pixels, 0xFFEF4444u32)).to_be(true)
expect(cache.animation_frame_due(1015)).to_be(false)
expect(cache.animation_frame_due(1016)).to_be(true)

val middle = simple_web_content_frame_cached_at_time(
    cache, "animated", 2, revision, "glass_dark", "Animation",
    body, 64, 48, 0, 1500
)
assert_not_equal(middle.checksum, first.checksum)
val last = simple_web_content_frame_cached_at_time(
    cache, "animated", 3, revision, "glass_dark", "Animation",
    body, 64, 48, 0, 2000
)
expect(contains_pixel(last.pixels, 0xFF2563EBu32)).to_be(true)
assert_not_equal(last.checksum, middle.checksum)
expect(cache.animation_frame_due(2001)).to_be(false)
```

</details>

#### keeps shared-WM content requests free of a duplicate inner titlebar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = simple_web_content_render_request_with_theme("glass_dark", "Runtime title", "<p>body</p>", 80, 40)
expect(req.body_html.contains("wm-app-titlebar")).to_be(false)
expect(req.body_html.contains("wm-app-content")).to_be(true)
expect(req.body_html.contains("widget-panel")).to_be(true)
```

</details>

#### composes Aetheric package CSS instead of a renderer-owned palette

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = simple_web_content_render_request_with_theme("aetheric_dark", "Runtime title", "<p>body</p>", 80, 40)
expect(req.css).to_contain("--ui-accent: #adc6ff")
expect(req.css).to_contain(".widget-panel")
expect(req.css).to_contain("--theme-icon-terminal")
expect(req.css).to_contain("backdrop-filter")
expect(req.body_html).to_contain("data-wm-theme-material-mode='engine2d-cpu-composited-material-v1'")
expect(req.body_html).to_contain("data-wm-theme-fallback='solid-material'")
expect(req.body_html).to_contain("data-wm-theme-bg='#1F1F21'")
expect(req.body_html).to_contain("data-wm-theme-fg='#E4E2E4'")
expect(req.css.contains("#dbeafe")).to_be(false)
expect(req.css.contains("#f8fafc")).to_be(false)
```

</details>

#### serializes production WM aliases through the canonical request

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "<section class='wm-window focused'><header class='wm-titlebar'><h1 class='wm-title'>Aetheric</h1></header></section>"
val html = simple_web_content_full_html_with_theme("aetheric_dark", "Aetheric", body, 320, 200)
expect(html).to_contain("<html data-wm-theme=\"aetheric_dark\"")
expect(html).to_contain("data-wm-theme-fallback='solid-material'")
expect(html).to_contain(".widget-dialog, .wm-window")
expect(html).to_contain(".widget-label, .wm-title")
expect(html).to_contain(".widget-tab-bar, .wm-titlebar")
expect(html).to_contain(body)
```

</details>

#### does not overlay the legacy blue slate WM heuristic on themed content

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = web_render_pixel_artifact_cache(80, 40, "software")
val revision = simple_web_content_revision_with_theme("aetheric_dark", "Theme", "<div>content</div>", 80, 40, 0)
val frame = simple_web_content_frame_cached(cache, "theme-window", 1, revision, "aetheric_dark", "Theme", "<div>content</div>", 80, 40, 0)
expect(contains_pixel(frame.pixels, 0xFF1F1F21u32)).to_be(true)
expect(contains_pixel(frame.pixels, 0xFF2050A0u32)).to_be(false)
expect(contains_pixel(frame.pixels, 0xFF182230u32)).to_be(false)
```

</details>

#### realizes the declared solid fallback instead of the translucent surface RGB

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<div data-wm-theme-fallback='solid-material' data-wm-theme-bg='#123456' data-wm-theme-fg='#FEDCBA' style='width:24px;height:16px;background:rgba(255,0,0,0.2);color:#FFFFFF;backdrop-filter:blur(12px)'>fallback</div>"
val pixels = simple_web_layout_render_html_software_pixels(html, 24, 16)
expect(contains_pixel(pixels, 0xFF123456u32)).to_be(true)
expect(contains_pixel(pixels, 0xFFFEDCBAu32)).to_be(true)
```

</details>

#### clears an earlier multilayer background when realizing the WM fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<div data-wm-theme-fallback='solid-material' data-wm-theme-bg='#123456' data-wm-theme-fg='#FEDCBA' style='width:24px;height:16px;background:radial-gradient(circle,#FF0000,#0000FF),rgba(255,0,0,0.2);backdrop-filter:blur(12px)'>fallback</div>"
val software = simple_web_layout_render_html_software_result(html, 24, 16)
val draw_ir = simple_web_layout_render_html_readback_engine2d_result(html, 24, 16, "software")
expect(contains_pixel(software.pixels, 0xFF123456u32)).to_be(true)
expect(software.material_fallback.kind).to_equal("solid-material")
expect(software.material_fallback.material_sha256.len()).to_equal(64)
expect(draw_ir.material_fallback.kind).to_equal("solid-material")
expect(draw_ir.material_fallback.material_sha256).to_equal(software.material_fallback.material_sha256)
```

</details>

#### honors a later background shorthand after background-image none

- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val later_none = simple_web_layout_render_html_software_pixels("<div style='width:24px;height:16px;background:radial-gradient(circle,#FF0000,#0000FF);background-image:none'>x</div>", 24, 16)
val later_gradient = simple_web_layout_render_html_software_pixels("<div style='width:24px;height:16px;background-image:none;background:radial-gradient(circle,#FF0000,#0000FF)'>x</div>", 24, 16)
assert_not_equal(later_gradient, later_none)
```

</details>

#### propagates stable realized fallback provenance through cache hits

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = simple_web_content_render_request_with_theme("aetheric_dark", "Theme", "<p>fallback</p>", 80, 40)
val cache = web_render_pixel_artifact_cache(80, 40, "software")
val first = cache.request_to_pixel_artifact(req)
val second = cache.request_to_pixel_artifact(req)
expect(first.material_fallback.kind).to_equal("cpu-composited-material")
expect(first.material_fallback.reason).to_equal("native-device-backdrop-path-pending")
expect(first.material_fallback.material_sha256.len()).to_equal(64)
expect(second.material_fallback.material_sha256).to_equal(first.material_fallback.material_sha256)
expect(cache.hits()).to_equal(1)
```

</details>

#### keeps Aetheric fallback provenance for an empty runtime window

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = web_render_pixel_artifact_cache(80, 40, "software")
val revision = simple_web_content_revision_with_theme("aetheric_dark", "System Console", "", 80, 40, 0)
val frame = simple_web_content_frame_cached(cache, "empty-window", 1, revision, "aetheric_dark", "System Console", "", 80, 40, 0)
expect(frame.material_fallback_kind).to_equal("cpu-composited-material")
expect(frame.material_fallback_reason).to_equal("native-device-backdrop-path-pending")
expect(frame.material_fallback_sha256.len()).to_equal(64)
expect(wm_content_frame_web_provenance_valid(frame)).to_be(true)
```

</details>

#### hashes resolved fallback colors rather than CSS spelling

- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hex_req = WebRenderRequest.html(WEB_RENDER_TARGET_SIMPLE_WEB, "hex", "<div data-wm-theme-fallback='solid-material' data-wm-theme-bg='#123456' data-wm-theme-fg='#FEDCBA'>x</div>", "", "", 24, 16)
val rgb_req = WebRenderRequest.html(WEB_RENDER_TARGET_SIMPLE_WEB, "rgb", "<div data-wm-theme-fallback='solid-material' data-wm-theme-bg='rgb(18,52,86)' data-wm-theme-fg='rgb(254,220,186)'>x</div>", "", "", 24, 16)
val changed_req = WebRenderRequest.html(WEB_RENDER_TARGET_SIMPLE_WEB, "changed", "<div data-wm-theme-fallback='solid-material' data-wm-theme-bg='#654321' data-wm-theme-fg='#FEDCBA'>x</div>", "", "", 24, 16)
val hex_artifact = web_render_request_to_pixel_artifact(hex_req)
val rgb_artifact = web_render_request_to_pixel_artifact(rgb_req)
val changed_artifact = web_render_request_to_pixel_artifact(changed_req)
expect(hex_artifact.material_fallback.kind).to_equal("solid-material")
expect(rgb_artifact.material_fallback.kind).to_equal("solid-material")
expect(hex_artifact.material_fallback.material_sha256.len()).to_equal(64)
expect(hex_artifact.material_fallback.material_sha256).to_equal(rgb_artifact.material_fallback.material_sha256)
assert_not_equal(hex_artifact.material_fallback.material_sha256, changed_artifact.material_fallback.material_sha256)
```

</details>

#### does not report fallback provenance for ordinary opaque HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_SIMPLE_WEB, "plain", "<div style='background:#123456;color:#FEDCBA'>x</div>", "", "", 24, 16)
val artifact = web_render_request_to_pixel_artifact(req)
expect(artifact.material_fallback.kind).to_equal("none")
```

</details>

#### uses the same realized fallback hash for software and Draw IR execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<div data-wm-theme-fallback='solid-material' data-wm-theme-bg='#123456' data-wm-theme-fg='#FEDCBA' style='width:24px;height:16px;background:rgba(255,0,0,0.2);color:#FFFFFF;backdrop-filter:blur(12px)'>fallback</div>"
val software = simple_web_layout_render_html_software_result(html, 24, 16)
val draw_ir = simple_web_layout_render_html_readback_engine2d_result(html, 24, 16, "software")
expect(software.material_fallback.kind).to_equal("solid-material")
expect(draw_ir.material_fallback.kind).to_equal("solid-material")
expect(software.material_fallback.material_sha256.len()).to_equal(64)
expect(draw_ir.material_fallback.material_sha256).to_equal(software.material_fallback.material_sha256)
```

</details>

#### keeps compatibility aliases package-owned and themes cache revisions

- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val canonical = simple_web_content_revision_with_theme("aetheric_dark", "title", "<p>body</p>", 80, 40, 0)
val alias = simple_web_content_revision_with_theme("glass_light", "title", "<p>body</p>", 80, 40, 0)
val missing = simple_web_content_revision_with_theme("missing_theme_for_revision_test", "title", "<p>body</p>", 80, 40, 0)
expect(alias).to_equal(canonical)
assert_not_equal(missing, canonical)
```

</details>

#### keeps unchanged content identity stable and changes it on mutation

- assert not equal
   - Expected: first.checksum equals `second.checksum`
   - Expected: first.pixels equals `second.pixels`
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first_cache = web_render_pixel_artifact_cache(96, 48, "software")
val second_cache = web_render_pixel_artifact_cache(96, 48, "software")
val changed_cache = web_render_pixel_artifact_cache(96, 48, "software")
val stable_revision = simple_web_content_revision("动态 title", "<b>same pixels</b>", 96, 48, 0)
val repeated_revision = simple_web_content_revision("动态 title", "<b>same pixels</b>", 96, 48, 0)
val changed_revision = simple_web_content_revision("动态 title", "<b>changed pixels</b>", 96, 48, 0)
val first = simple_web_content_frame_cached(first_cache, "w", 1, stable_revision, "glass_dark", "动态 title", "<b>same pixels</b>", 96, 48, 0)
val second = simple_web_content_frame_cached(second_cache, "w", 2, repeated_revision, "glass_dark", "动态 title", "<b>same pixels</b>", 96, 48, 0)
val changed = simple_web_content_frame_cached(changed_cache, "w", 3, changed_revision, "glass_dark", "动态 title", "<b>changed pixels</b>", 96, 48, 0)
expect(stable_revision).to_equal(repeated_revision)
assert_not_equal(stable_revision, changed_revision)
expect(first.checksum).to_equal(second.checksum)
expect(first.pixels).to_equal(second.pixels)
assert_not_equal(first.checksum, changed.checksum)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/simple_web_window_renderer_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Web compositor adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
