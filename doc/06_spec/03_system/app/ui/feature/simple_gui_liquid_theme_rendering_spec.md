# Simple GUI Liquid Theme Rendering Specification

> Covers `browser_cpu_raster_css_overrides` (`src/app/ui.browser/backend.spl`), Liquid Dark/Light palette wiring (`src/app/ui.web/html.spl`, `src/app/ui.web/html_css.spl`), flex layout gap/shrink rules (`src/app/ui.render/html_widgets.spl`), and end-to-end Pure-Simple vs sRGB Chrome rendering across `.ui.sdn` apps.

<!-- sdn-diagram:id=simple_gui_liquid_theme_rendering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_gui_liquid_theme_rendering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_gui_liquid_theme_rendering_spec -> ui_browser_backend
simple_gui_liquid_theme_rendering_spec -> ui_render_html_widgets
simple_gui_liquid_theme_rendering_spec -> ui_web_html
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_gui_liquid_theme_rendering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

## Chrome (sRGB) vs Pure-Simple Parity Summary (`gui_liquid` & `lq06`)

Captured using Electron with `--force-color-profile=srgb` against Pure-Simple `BrowserBackend(cpu_simd, pure_simple)` with `browser_cpu_raster_css_overrides`:

| Case | Theme | Viewport | Exact | <=2 | <=12 | <=32 | MAD |
|------|-------|----------|------:|----:|-----:|-----:|----:|
| `demo_kitchen_sink.ui.sdn` (`lq06`) | `fluid_dark` | `960x640` | `0.0%` | `14.01%` | `76.01%` | `90.39%` | `12.96` |
| `demo_button_checkbox_dropdown.ui.sdn` | `fluid_light` | `640x420` | `8.4%` | `50.87%` | `64.2%` | `92.34%` | `7.95` |
| `demo_button_checkbox_dropdown.ui.sdn` | `glass_dark` | `640x420` | `1.01%` | `39.78%` | `65.37%` | `78.66%` | `9.44` |
| `demo_scroll_textarea.ui.sdn` | `glass_dark` | `640x420` | `1.65%` | `42.0%` | `87.02%` | `93.73%` | `9.0` |
| `simpleos_web_wm.ui.sdn` | `glass_obsidian_dark` | `640x420` | `0.08%` | `6.51%` | `28.66%` | `95.94%` | `12.46` |

<details>
<summary>Full Scenario Manual</summary>

# Simple GUI Liquid Theme Rendering Specification

## Scenarios

### Simple GUI Liquid Theme Rendering System Spec

#### 1. preserves radial and linear ambient aura and specular borders in CPU raster overrides across all four Liquid Glass themes

1. Call `browser_cpu_raster_css_overrides` for `"fluid_dark"`, `"glass_dark"`, `"glass_obsidian_dark"`, and `"fluid_light"`.
   - Expected: disables `backdrop-filter`, `box-shadow`, and `body::before, body::after`.
   - Expected: keeps `radial-gradient(...)` and `linear-gradient(...)` on `body`.
   - Expected: keeps `border-top-color: rgba(255,255,255,0.22) !important;` on dark glass themes and `rgba(255,255,255,0.85) !important;` on `fluid_light`.

#### 2. emits distinct Liquid Dark and Liquid Light palette variables in both html.spl and html_css.spl

1. Call `generate_css("fluid_dark")`, `generate_css("fluid_light")`, and `html_css.generate_css(...)`.
   - Expected: `fluid_dark` emits `--ui-bg: #080d17;` and `--ui-accent: #4da3ff;`.
   - Expected: `fluid_light` emits `--ui-bg: #faf9fe;`, `--ui-text: #1a1b1f;`, and `--ui-accent: #0058bc;`.

#### 3. emits gap and min-width/min-height zero on vbox and hbox panels and valid HTML widget focus states

1. Render `column`, `row`, scaled `panel`, focused `text_input`, `tabs`, and `scroll` via `render_html_widget`.
   - Expected: `column` and `row` emit `gap: 12px; min-width: 0; min-height: 0;`.
   - Expected: `panel(..., 30)` emits `width: 240px; min-width: 210px; flex: none;` and `panel(..., 250)` emits `width: 250px; flex: none;`.
   - Expected: focused `text_input` emits `data-target-id` and `data-focused="true"`, while unfocused `text_field` does not.

#### 4. builds themed HTML documents with Liquid Glass styling for real .ui.sdn example apps

1. Parse and render HTML+CSS for `demo_kitchen_sink.ui.sdn` (`fluid_dark`), `demo_button_checkbox_dropdown.ui.sdn` (`fluid_light` and `glass_dark`), `demo_scroll_textarea.ui.sdn` (`glass_dark`), and `simpleos_web_wm.ui.sdn` (`glass_obsidian_dark`).
   - Expected: each output carries matching `data-wm-theme` root attribute, Liquid Glass ambient aura rules, and widget content.

#### 5. rasterizes SimpleOS Web WM via Pure-Simple BrowserBackend in cpu_simd mode with full viewport pixel buffer

1. Call `BrowserBackend.create(640, 420, "cpu_simd", "pure_simple")` and `render_frame` on `simpleos_web_wm.ui.sdn` (`glass_obsidian_dark`).
   - Expected: `backend.last_artifact_pixels` equals `268800`.
   - Expected: `backend.content_height` is greater than `0`.
   - Expected: `backend.last_artifact_html` contains `border-top-color: rgba(255,255,255,0.22) !important;`.

</details>
