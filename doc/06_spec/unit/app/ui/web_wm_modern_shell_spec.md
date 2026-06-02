# web_wm_modern_shell_spec

Verifies the first modern Simple Web WM slice at the contract level.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/web_wm_modern_shell_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the first modern Simple Web WM slice at the contract level.
    The shell remains server-authoritative, so this spec checks generated CSS
    and browser-side lifecycle hooks rather than issuing local state mutations.

## Scenarios

### Simple Web WM modern shell contract

#### generates rounded translucent WM chrome and motion CSS

<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_wm_html_page("glass_dark", "Simple WM", 8080)
expect(html).to_contain(".wm-window.opening")
expect(html).to_contain("#wm-desktop::before")
expect(html).to_contain("z-index: 0")
expect(html).to_contain(".wm-window { position: absolute; z-index: 20")
expect(html).to_contain("@keyframes wm-window-open")
expect(html).to_contain("@keyframes wm-window-close")
expect(html).to_contain("@keyframes wm-window-minimize")
expect(html).to_contain("@keyframes widget-pop-in")
expect(html).to_contain("@keyframes wm-bg-drift")
expect(html).to_contain("prefers-reduced-motion")
expect(html).to_contain("data-wm-motion=reduced")
expect(html).to_contain("data-wm-motion=off")
expect(html).to_contain("transition-duration: 80ms")
expect(html).to_contain(".wm-titlebar-icon")
expect(html).to_contain(".wm-round-icon")
expect(html).to_contain(".wm-icon-normalized-square")
expect(html).to_contain(".wm-icon-image")
expect(html).to_contain(".wm-icon-glyph")
expect(html).to_contain(".wm-title-context")
expect(html).to_contain(".wm-title-input")
expect(html).to_contain(".wm-command-bar")
expect(html).to_contain(".wm-command-palette")
expect(html).to_contain(".wm-command-palette-input")
expect(html).to_contain(".wm-command-item")
expect(html).to_contain(".wm-taskbar-icon")
expect(html).to_contain("translateY(-3px) scale(1.04)")
expect(html).to_contain("border-radius: 999px")
```

</details>

#### client applies lifecycle and icon classes without protocol changes

<details>
<summary>Executable SPipe</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val js = rt_file_read_text("src/app/ui.web/wm.js")
val retained = rt_file_read_text("src/app/ui.web/retained_renderer.js")
expect(js).to_contain("_makeTaskbarIcon")
expect(js).to_contain("WM_MOTION_STORAGE_KEY")
expect(js).to_contain("simple.wm.motion")
expect(js).to_contain("simpleWmSetMotion")
expect(js).to_contain("_applyMotionPreference")
expect(js).to_contain("_normalizeMotionPreference")
expect(js).to_contain("_ensureCommandPalette")
expect(js).to_contain("_commandPaletteCommands")
expect(js).to_contain("_toggleCommandPalette")
expect(js).to_contain("_moveCommandPaletteSelection")
expect(js).to_contain("_executeCommandPaletteAction")
expect(js).to_contain("Open Simple IDE")
expect(js).to_contain("Set motion: off")
expect(js).to_contain("e.key.toLowerCase() === 'k'")
expect(js).to_contain("_makeRoundIcon")
expect(js).to_contain("_isImageIcon")
expect(js).to_contain("square-to-round")
expect(js).to_contain("glyph-to-round")
expect(js).to_contain("_makeTitleInput")
expect(js).to_contain("_markWindowLifecycle")
expect(js).to_contain("wm-titlebar-icon")
expect(js).to_contain("wm-command-bar")
expect(js).to_contain("wm-btn-close")
expect(retained).to_contain("_makeSurfaceIcon")
expect(retained).to_contain("_makeRoundIcon")
expect(retained).to_contain("_isImageIcon")
expect(retained).to_contain("square-to-round")
expect(retained).to_contain("_makeTitleInput")
expect(retained).to_contain("_markLifecycle")
expect(retained).to_contain("wm-command-bar")
expect(retained).to_contain("closing")
expect(retained).to_contain("minimizing")
```

</details>

#### generates a standalone modern WM visual preview fixture

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preview = generate_wm_modern_preview_html("glass_dark")
expect(preview).to_contain("data-preview=\"modern-wm\"")
expect(preview).to_contain("data-wm-motion=\"standard\"")
expect(preview).to_contain("wm-window focused opening")
expect(preview).to_contain("wm-window restoring")
expect(preview).to_contain("wm-traffic-lights")
expect(preview).to_contain("wm-title-input wm-command-bar")
expect(preview).to_contain("wm-command-palette")
expect(preview).to_contain("wm-command-palette-input")
expect(preview).to_contain("wm-command-item active")
expect(preview).to_contain("Set motion: reduced")
expect(preview).to_contain("widget-menubar")
expect(preview).to_contain("widget-panel focused")
expect(preview).to_contain("widget-statusbar")
expect(preview).to_contain("wm-taskbar-item active")
expect(preview).to_contain("wm-icon-normalized-square")
expect(preview).to_contain("contrast_ratio_x100=450")
```

</details>

#### writes a browser-loadable modern WM preview evidence artifact

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "build/simple_wm_modern_preview.html"
expect(write_wm_modern_preview_html(path, "glass_dark"))
val written = rt_file_read_text(path)
expect(written).to_contain("<!DOCTYPE html>")
expect(written).to_contain("Simple WM Modern Preview")
expect(written).to_contain("wm-command-palette")
expect(written).to_contain("wm-window focused opening")
expect(written).to_contain("wm-taskbar-item active")
val report = wm_modern_preview_evidence_report(path, "glass_dark")
expect(report).to_contain("wm_modern_preview")
expect(report).to_contain("path=build/simple_wm_modern_preview.html")
expect(report).to_contain("command_palette=true")
expect(report).to_contain("normalized_icons=true")
```

</details>

#### reports theme quality for color size layout motion and shell affordances

<details>
<summary>Executable SPipe</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = wm_theme_quality_report("glass_dark")
expect(report.passed)
expect(report.color_checked)
expect(report.contrast_ratio_x100).to_be_greater_than(449)
expect(report.contrast_delta).to_be_greater_than(96)
expect(report.semantic_tokens)
expect(report.stable_layout)
expect(report.size_layout_configured)
expect(report.titlebar_height_px).to_equal(38)
expect(report.window_min_width_px).to_equal(200)
expect(report.window_min_height_px).to_equal(120)
expect(report.title_input_min_width_px).to_equal(140)
expect(report.taskbar_icon_size_px).to_equal(26)
expect(report.rounded_shapes)
expect(report.round_icon_masking)
expect(report.round_icon_converter)
expect(report.round_scrollbars)
expect(report.translucent_shell)
expect(report.lifecycle_motion)
expect(report.widget_motion)
expect(report.reduced_motion)
expect(report.motion_verbosity_control)
expect(report.preview_fixture_ready)
expect(report.command_context_ready)
expect(report.command_palette_ready)
expect(report.title_input_ready)
expect(report.visual_layering_ready)
expect(wm_theme_quality_summary("glass_dark")).to_contain("status=pass")
expect(wm_theme_quality_summary("glass_dark")).to_contain("contrast_ratio_x100=")
expect(wm_theme_quality_summary("glass_dark")).to_contain("titlebar_height_px=38")
expect(wm_theme_quality_summary("glass_dark")).to_contain("visual_layering_ready=true")
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

