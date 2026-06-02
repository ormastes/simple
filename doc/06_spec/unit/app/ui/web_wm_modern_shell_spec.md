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

Runnable source: 71 lines folded for reproduction.
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
expect(html).to_contain("@keyframes wm-widget-float")
expect(html).to_contain("@keyframes wm-bg-drift")
expect(html).to_contain("@keyframes wm-snap-pulse")
expect(html).to_contain(".wm-snap-preview")
expect(html).to_contain(".wm-snap-preview.active")
expect(html).to_contain("data-snap-zone=left")
expect(html).to_contain("data-snap-zone=right")
expect(html).to_contain("data-snap-zone=full")
expect(html).to_contain(".wm-desktop-widgets")
expect(html).to_contain(".wm-desktop-widgets.collapsed")
expect(html).to_contain(".wm-desktop-widget")
expect(html).to_contain(".wm-desktop-widget-label")
expect(html).to_contain(".wm-desktop-widget-value")
expect(html).to_contain(".wm-desktop-widget-meta")
expect(html).to_contain(".wm-window-overview")
expect(html).to_contain(".wm-overview-grid")
expect(html).to_contain(".wm-overview-card")
expect(html).to_contain(".wm-overview-card.active")
expect(html).to_contain(".wm-overview-icon")
expect(html).to_contain("@keyframes wm-overview-in")
expect(html).to_contain(".wm-control-center")
expect(html).to_contain(".wm-control-center[hidden]")
expect(html).to_contain(".wm-control-group")
expect(html).to_contain(".wm-control-button")
expect(html).to_contain("@keyframes wm-control-in")
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
expect(html).to_contain(".wm-app-launcher")
expect(html).to_contain(".wm-app-launcher[hidden]")
expect(html).to_contain(".wm-app-launcher-tile")
expect(html).to_contain("@keyframes wm-launcher-in")
expect(html).to_contain(".wm-shortcut-overlay")
expect(html).to_contain(".wm-shortcut-overlay[hidden]")
expect(html).to_contain(".wm-shortcut-row")
expect(html).to_contain("@keyframes wm-shortcuts-in")
expect(html).to_contain(".wm-window-context-menu")
expect(html).to_contain(".wm-window-context-menu[hidden]")
expect(html).to_contain(".wm-window-context-item")
expect(html).to_contain("@keyframes wm-context-menu-in")

expect(html).to_contain(":focus-visible")
expect(html).to_contain("outline-offset: 3px")
expect(html).to_contain(".wm-traffic-lights button::before")
expect(html).to_contain("inset: -8px")
expect(html).to_contain(".wm-command-palette-input { width: 100%; height: 44px")
expect(html).to_contain("min-height: 44px")
expect(html).to_contain(".wm-taskbar-icon")
expect(html).to_contain("translateY(-3px) scale(1.04)")
expect(html).to_contain("border-radius: 999px")
```

</details>

#### client applies lifecycle and icon classes without protocol changes

<details>
<summary>Executable SPipe</summary>

Runnable source: 95 lines folded for reproduction.
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
expect(js).to_contain("_activateTaskbarItem")
expect(js).to_contain("Open Simple IDE")
expect(js).to_contain("Set motion: off")
expect(js).to_contain("Set transparency: standard")
expect(js).to_contain("Set transparency: reduced")
expect(js).to_contain("Set transparency: off")
expect(js).to_contain("Set wallpaper: aurora")
expect(js).to_contain("Set wallpaper: mesh")
expect(js).to_contain("Set wallpaper: solid")
expect(js).to_contain("Open widget gallery")
expect(js).to_contain("_ensureAppLauncher")
expect(js).to_contain("_toggleAppLauncher")
expect(js).to_contain("_renderAppLauncher")
expect(js).to_contain("_executeAppLauncherSelection")
expect(js).to_contain("Cmd Space")
expect(js).to_contain("e.key === ' '")
expect(js).to_contain("_ensureShortcutOverlay")
expect(js).to_contain("_toggleShortcutOverlay")
expect(js).to_contain("Show keyboard shortcuts")
expect(js).to_contain("Cmd /")
expect(js).to_contain("e.key === '/'")
expect(js).to_contain("e.key.toLowerCase() === 'k'")
expect(js).to_contain("role', 'listbox'")
expect(js).to_contain("role', 'option'")
expect(js).to_contain("aria-selected")
expect(js).to_contain("Window taskbar")
expect(js).to_contain("a.display_name || a.app_id")
expect(js).to_contain("w.minimized ? 'Restore' : 'Focus'")
expect(js).to_contain("w.title || w.window_id")
expect(js).to_contain("ev.key !== 'Enter' && ev.key !== ' '")
expect(js).to_contain("Close window")
expect(js).to_contain("Minimize window")
expect(js).to_contain("Maximize window")
expect(js).to_contain("_makeRoundIcon")
expect(js).to_contain("_isImageIcon")
expect(js).to_contain("square-to-round")
expect(js).to_contain("glyph-to-round")
expect(js).to_contain("_makeTitleInput")
expect(js).to_contain("_markWindowLifecycle")
expect(js).to_contain("_ensureSnapPreview")
expect(js).to_contain("_detectSnapZone")
expect(js).to_contain("_snapRectForZone")
expect(js).to_contain("_applySnapPreview")
expect(js).to_contain("_clearSnapPreview")
expect(js).to_contain("snap_zone")
expect(js).to_contain("_ensureDesktopWidgets")
expect(js).to_contain("_makeDesktopWidget")
expect(js).to_contain("_toggleDesktopWidgets")
expect(js).to_contain("Toggle desktop widgets")
expect(js).to_contain("wm-desktop-widget")
expect(js).to_contain("_ensureWindowOverview")
expect(js).to_contain("_toggleWindowOverview")
expect(js).to_contain("_renderWindowOverview")
expect(js).to_contain("_overviewWindows")
expect(js).to_contain("_makeOverviewCard")
expect(js).to_contain("_focusWindowById")
expect(js).to_contain("Show window overview")
expect(js).to_contain("wm-window-overview")
expect(js).to_contain("wm-overview-card")
expect(js).to_contain("_ensureControlCenter")
expect(js).to_contain("_toggleControlCenter")
expect(js).to_contain("_renderControlCenter")
expect(js).to_contain("_makeControlCenterButton")
expect(js).to_contain("_setMotionFromControlCenter")
expect(js).to_contain("Open control center")
expect(js).to_contain("wm-control-center")
expect(js).to_contain("wm-control-button")
expect(js).to_contain("wm-titlebar-icon")
expect(js).to_contain("wm-command-bar")
expect(js).to_contain("wm-btn-")
expect(retained).to_contain("_makeSurfaceIcon")
expect(retained).to_contain("_makeRoundIcon")
expect(retained).to_contain("_isImageIcon")
expect(retained).to_contain("square-to-round")
expect(retained).to_contain("_makeTitleInput")
expect(retained).to_contain("_markLifecycle")
expect(retained).to_contain("wm-command-bar")
expect(retained).to_contain("closing")
expect(retained).to_contain("minimizing")
expect(retained).to_contain("Close window")
expect(retained).to_contain("Minimize window")
expect(retained).to_contain("Maximize window")
```

</details>

#### generates a standalone modern WM visual preview fixture

<details>
<summary>Executable SPipe</summary>

Runnable source: 66 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preview = generate_wm_modern_preview_html("glass_dark")
expect(preview).to_contain("data-preview=\"modern-wm\"")
expect(preview).to_contain("data-wm-motion=\"standard\"")
expect(preview).to_contain("wm-window focused opening")
expect(preview).to_contain("wm-window restoring")
expect(preview).to_contain("wm-snap-preview active")
expect(preview).to_contain("data-snap-zone=\"right\"")
expect(preview).to_contain("aria-hidden=\"true\"")
expect(preview).to_contain("wm-desktop-widgets")
expect(preview).to_contain("wm-widget-clock")
expect(preview).to_contain("wm-widget-system")
expect(preview).to_contain("wm-widget-workspace")
expect(preview).to_contain("aria-label=\"Desktop widgets\"")
expect(preview).to_contain("aria-label=\"Window overview\"")
expect(preview).to_contain("wm-window-overview")
expect(preview).to_contain("wm-overview-card active")
expect(preview).to_contain("wm-overview-card-title")
expect(preview).to_contain("wm-overview-card-meta")
expect(preview).to_contain("Show window overview")
expect(preview).to_contain("aria-label=\"WM control center\"")
expect(preview).to_contain("wm-control-center")
expect(preview).to_contain("wm-control-button active")
expect(preview).to_contain("role=\"menu\" aria-label=\"Window context menu\"")
expect(preview).to_contain("wm-window-context-item active")
expect(preview).to_contain("data-context-action=\"focus\"")
expect(preview).to_contain("data-context-action=\"snap_left\"")
expect(preview).to_contain("data-context-action=\"snap_right\"")
expect(preview).to_contain("data-context-action=\"close\"")
expect(preview).to_contain("role=\"listbox\" aria-label=\"Window command suggestions\"")
expect(preview).to_contain("wm-title-suggestion-item active")
expect(preview).to_contain("wm-title-suggestion-label")
expect(preview).to_contain("wm-title-suggestion-meta")
expect(preview).to_contain("workspace search")
expect(preview).to_contain("role=\"dialog\" aria-label=\"App launcher\"")
expect(preview).to_contain("wm-app-launcher-tile active")
expect(preview).to_contain("data-app-id=\"simple.ide\"")
expect(preview).to_contain("wm-app-launcher-name")
expect(preview).to_contain("role=\"dialog\" aria-label=\"Keyboard shortcuts\"")
expect(preview).to_contain("wm-shortcut-title")
expect(preview).to_contain("wm-shortcut-row")
expect(preview).to_contain("Cmd K")
expect(preview).to_contain("Cmd L")
expect(preview).to_contain("Standard motion")
expect(preview).to_contain("Reduced motion")
expect(preview).to_contain("Motion off")
expect(preview).to_contain("Open control center")
expect(preview).to_contain("wm-traffic-lights")
expect(preview).to_contain("wm-title-input wm-command-bar")
expect(preview).to_contain("wm-command-palette")
expect(preview).to_contain("wm-command-palette-input")
expect(preview).to_contain("wm-command-item active")
expect(preview).to_contain("role=\"listbox\"")
expect(preview).to_contain("role=\"option\"")
expect(preview).to_contain("aria-selected=\"true\"")
expect(preview).to_contain("aria-label=\"Close window\"")
expect(preview).to_contain("aria-label=\"Minimize window\"")
expect(preview).to_contain("aria-label=\"Maximize window\"")
expect(preview).to_contain("role=\"navigation\" aria-label=\"Window taskbar\"")
expect(preview).to_contain("aria-label=\"Focus Simple IDE\"")
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

Runnable source: 16 lines folded for reproduction.
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
expect(report).to_contain("control_center=true")
expect(report).to_contain("window_overview=true")
expect(report).to_contain("normalized_icons=true")
expect(report).to_contain("desktop_widgets=true")
```

</details>

#### reports theme quality for color size layout motion and shell affordances

<details>
<summary>Executable SPipe</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = wm_theme_quality_report("glass_dark")
expect(report.passed)
expect(report.color_checked)
expect(report.contrast_ratio_x100).to_be_greater_than(449)
expect(report.contrast_ratio_x100).to_be_greater_than(1700)
expect(report.contrast_ratio_x100).to_be_less_than(1900)
expect(report.contrast_delta).to_be_greater_than(96)
expect(report.semantic_tokens)
expect(report.stable_layout)
expect(report.size_layout_configured)
expect(report.titlebar_height_px).to_equal(38)
expect(report.window_min_width_px).to_equal(200)
expect(report.window_min_height_px).to_equal(120)
expect(report.title_input_min_width_px).to_equal(140)
expect(report.taskbar_icon_size_px).to_equal(26)
expect(report.command_palette_max_width_px).to_equal(680)
expect(report.control_center_max_width_px).to_equal(320)
expect(report.desktop_widget_max_width_px).to_equal(260)
expect(report.overview_card_min_width_px).to_equal(180)
expect(report.touch_target_min_height_px).to_equal(44)
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
expect(report.accessible_controls_ready)
expect(report.snap_assist_ready)
expect(report.desktop_widgets_ready)
expect(report.wallpaper_picker_ready)
expect(report.app_launcher_ready)
expect(report.shortcut_overlay_ready)
expect(report.widget_gallery_ready)
expect(report.window_overview_ready)
expect(report.control_center_ready)
expect(report.responsive_layout_ready)
expect(wm_theme_quality_summary("glass_dark")).to_contain("status=pass")
expect(wm_theme_quality_summary("glass_dark")).to_contain("contrast_ratio_x100=")
expect(wm_theme_quality_summary("glass_dark")).to_contain("titlebar_height_px=38")
expect(wm_theme_quality_summary("glass_dark")).to_contain("command_palette_max_width_px=680")
expect(wm_theme_quality_summary("glass_dark")).to_contain("control_center_max_width_px=320")
expect(wm_theme_quality_summary("glass_dark")).to_contain("desktop_widget_max_width_px=260")
expect(wm_theme_quality_summary("glass_dark")).to_contain("overview_card_min_width_px=180")
expect(wm_theme_quality_summary("glass_dark")).to_contain("touch_target_min_height_px=44")
expect(wm_theme_quality_summary("glass_dark")).to_contain("responsive_layout_ready=true")
expect(wm_theme_quality_summary("glass_dark")).to_contain("visual_layering_ready=true")
expect(wm_theme_quality_summary("glass_dark")).to_contain("accessible_controls_ready=true")
expect(wm_theme_quality_summary("glass_dark")).to_contain("snap_assist_ready=true")
expect(wm_theme_quality_summary("glass_dark")).to_contain("desktop_widgets_ready=true")
expect(wm_theme_quality_summary("glass_dark")).to_contain("wallpaper_picker_ready=true")
expect(wm_theme_quality_summary("glass_dark")).to_contain("app_launcher_ready=true")
expect(wm_theme_quality_summary("glass_dark")).to_contain("shortcut_overlay_ready=true")
expect(wm_theme_quality_summary("glass_dark")).to_contain("widget_gallery_ready=true")
expect(wm_theme_quality_summary("glass_dark")).to_contain("window_overview_ready=true")
expect(wm_theme_quality_summary("glass_dark")).to_contain("control_center_ready=true")
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

