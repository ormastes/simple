# System & Unit Test Plan: Simple Web Engine Completion (`release/1.0.0`)

- **Date:** 2026-11-28
- **Target Branch:** `release/1.0.0`
- **Requirements:** `REQ-WEB-001`..`REQ-WEB-008`, `NFR-WEB-001`..`NFR-WEB-005`

## 1. Test Coverage Matrix

| Req ID | SSpec Test File | Key Real Assertions (No Placeholders) |
|---|---|---|
| `REQ-WEB-001` | `test/01_unit/browser_engine/float_paint_stacking_order_chrome159_spec.spl` + `test/01_unit/browser_engine/float_fractional_height_clear_chrome159_spec.spl` | Float box (`float:left`/`right`) + descendant `#text` paint ABOVE overlapping later normal-flow block background on both Draw IR (`cpu_simd`) and raster (`software`) lanes at `k=1` and `k=4`, while normal-flow `#text` paints ABOVE the float. |
| `REQ-WEB-002` | `test/01_unit/browser_engine/grid_auto_track_template_chrome159_spec.spl` | Both wrapped `<div><div style="display:flex">` and direct `<div style="display:flex">` items inside `grid-template-columns: auto 1fr` size the `auto` track to max-content (`40px`, `%` margin = `0` intrinsically). |
| `REQ-WEB-003` | `test/01_unit/browser_engine/inline_item_layoutunit_ceil_pen_chrome159_spec.spl` + `flex_row_button_tabs_chrome159_spec.spl` + new button/input device-width spec | `@tag:in-development` removed; `<code>a</code> — renderable` exact pixel columns match Chrome 159; `<input type=button|submit>` and flex/inline buttons match Chrome `k=1`/`k=4` widths; `200px` button at `k=4` respects measure cap. |
| `REQ-WEB-004` | `test/01_unit/browser_engine/fractional_layout_followups_chrome159_spec.spl` | `vertical-align:top|bottom` device baseline at `k=4`, `inline-block` `hangs_from_baseline` at `k=1`, `clear` vs `margin-top`, SVG edge AA & post-clamp residual. |
| `REQ-WEB-005` | `test/03_system/app/browser/browser_interactive_window_spec.spl` | Click hit-test resolves `<a href>` & `<button>` targets, wheel delta clamps `scroll_y` in `[0, max_scroll_y]`, Back/Forward/Reload update session history, and `gui_window.spl` contains zero engine-render imports (JIT guard). |
| `REQ-WEB-006` | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine2d_resolver_agreement_spec.spl` + `web_render_draw_ir_material_fallback_spec.spl` | Facade and renderer report identical resolved backend + honest fallback receipts. |
| `REQ-WEB-008` | `scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs`, `scripts/check/check-widget-shells-crossengine-evidence.shs` | `mismatch_count=0` (Node bitmap), `>= 80%` Chrome/Electron non-text parity (macOS). |

## 2. Generated Spec Docs Policy
- Executable `.spl` specs live strictly under `test/`.
- Generated/manual Markdown manuals live under `doc/06_spec/` (`find doc/06_spec -name '*_spec.spl' | wc -l` MUST equal `0`).
- Every test uses built-in matchers (`to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`) and real pixel/DOM assertions.

---

## 3. 14-Variation Chrome (`Blink/Skia`) vs Pure-Simple Web Layout + JS/SimpleScript Event Comparison Matrix

The in-tree comparison suite (`examples/browser/html_layout_compare/variations.sdn`, `src/app/html_layout_compare/main.spl`, and `tools/electron-shell/html_layout_compare_app.js`) validates HTML/CSS/Text/Image and interactive event parity across 14 visual variations (`v01`–`v14`) and 6 JS/SimpleScript event scenarios (`e01`–`e06`), backed by 4 procedurally generated shared `SimpleOsHostGpuImageResource` PNG assets (`../assets/sunset.png` `160x96`, `../assets/avatar.png` `48x48`, `../assets/cube.png` `120x80`, `../assets/star.png` `20x20`).

### 3.1 Visual Variation Matrix (`v01`–`v14`) & macOS Reference Baseline
| ID | Title | Viewport | Category / Tags | Historical macOS Baseline (`Exact / <=12 / <=32 / MAD`) |
|---|---|---|---|---|
| `v01` | Flex Hero & Feature Cards | `520x340` | Flexbox, Hero, Images | `0.00% / 92.52% / 94.97% / 4.94` |
| `v02` | Editorial Float Left & Right Images | `520x340` | Float, Text Wrap, Clear | `0.00% / 70.26% / 80.33% / 22.60` |
| `v03` | CSS Grid 3x2 Media & Metric Dashboard | `520x340` | CSS Grid, Span 2, Metrics | `0.00% / 73.48% / 85.89% / 15.35` |
| `v04` | Holy Grail 3-Column App Workspace | `520x340` | App Shell, 3-Column, Sticky Chrome | `0.01% / 92.25% / 95.11% / 6.30` |
| `v05` | Media Object Comment & Reply Thread | `520x340` | Flex Row, Avatars, Nested Reply | `48.70% / 87.65% / 91.24% / 8.32` |
| `v06` | Image `object-fit` & Aspect Matrix | `520x340` | `object-fit`, `contain/cover/fill` | `0.00% / 66.20% / 78.20% / 17.86` |
| `v07` | Data Table with Inline Icons, Pills & `colspan` | `520x340` | HTML Table, `colspan`, Badges | `0.00% / 82.33% / 89.67% / 12.63` |
| `v08` | Positioned Pills, Caption Overlay & Z-Index | `520x340` | `relative`, `absolute`, `z-index` | `0.01% / 56.37% / 67.01% / 29.80` |
| `v09` | Inline Typography, Icons, Pills & Text Alignment | `520x340` | Inline Spans, Code Pills, Align | `82.02% / 87.10% / 89.04% / 12.60` |
| `v10` | Flex-Wrap Chips & Responsive Card Grid | `520x340` | `flex-wrap: wrap`, Gap, Multi-Row | `0.00% / 73.75% / 88.31% / 14.54` |
| `v11` | Profile Card & Form Controls Layout | `520x340` | Forms, Input/Select/Textarea | `0.06% / 79.38% / 91.74% / 10.87` |
| `v12` | Two-Column Lists, Blockquote & Captioned Figures | `520x340` | Columns, UL/OL, Blockquote | `43.93% / 77.09% / 87.26% / 13.47` |
| `v13` | Browser Feature Showcase (`browser_common_elements_showcase.html`) | `640x420` | Full App, Gradients, Showcase | `50.97% / 72.20% / 78.29% / 23.81` |
| `v14` | UI Kitchen Sink App Window (`demo_kitchen_sink.ui.sdn`) | `960x640` | Full App, Kitchen Sink, `960x640` | `6.66% / 53.27% / 84.16% / 18.27` |

### 3.2 Interactive JS / SimpleScript & Event Cases (`e01`–`e06`)
- `e01`: Click button & action dispatch (`BrowserSession.dispatch_dom_event` / `widget_hit`)
- `e02`: Pointer move & drag capture (`HostCompositor` / `widget_dispatch_pointer_move`)
- `e03`: `<select>` dropdown & `<details>` disclosure toggle
- `e04`: Keyboard input, Shift glyph propagation, & `Tab` focus / `blur` preedit cleanup
- `e05`: Wheel scroll delta clamping & linked scroll sync
- `e06`: JS / `SimpleScriptExecutor` DOM mutation & single-revision animation reconciliation

### 3.3 Runner, Viewer, Report Format & Parity Criteria
- **Runner (`src/app/html_layout_compare/main.spl`):** Synthesizes the 4 procedural image assets, renders variations via `simple_web_layout_render_html_software_pixels_with_images` + `encode_argb_to_png_rgb`, computes exact / `<=12px` / `<=32px` / `MAD` + `4x |diff|` heatmap PNGs when Chrome PNGs are present, writes **`compare_report.sdn`** by default, and exports `compare_manifest.json` + `compare_manifest.js` only when `--json` is passed.
- **Electron Runner & 4-Tab Studio (`tools/electron-shell/html_layout_compare_app.js` + `html_layout_compare_viewer.html`):** Offscreen Chrome capture (`--capture-chrome <dir> --pages <pages_dir>`) and `1440x920` dark UI supporting `1. All Variations Matrix`, `2. 1:1 / 2x Side-by-Side + HTML Source`, `3. Split Wipe & Rapid Flip`, and `4. JS & Simple Script + Events` (`script_events_manifest.js`).
- **Automated SSpec Gate:** `test/03_system/app/simple_web/feature/chrome_vs_simple_web_layout_compare_spec.spl` (manual at `doc/06_spec/03_system/app/simple_web/feature/chrome_vs_simple_web_layout_compare_spec.md`).
- **Parity Acceptance Criteria:** Zero render crashes/timeouts, valid non-empty PNG dimensions for every variation, accurate `compare_report.sdn` emission, and steady convergence on `<=12px` / `MAD` parity per lane without silent tolerances or skipped specs.

---

## 4. Suite 2 (Famous Web Pages), Suite 3 (Liquid Theme) & Multi-Script Lanes

### 4.1 Suite 2: Famous Web Page Rendering Diff (`fw01`–`fw06`, `640x420`)
| ID | Page / Layout Archetype | Viewport | Primary Focus |
|---|---|---|---|
| `fw01` | Google Search & Knowledge Panel | `640x420` | Search bar, two-column SERP + right knowledge card |
| `fw02` | Wikipedia Encyclopedia Article & Infobox | `640x420` | Float-right infobox table, lead prose, TOC |
| `fw03` | Hacker News Front Page Table & Ranks | `640x420` | Compact tabular row rhythm, header bar, metadata links |
| `fw04` | GitHub Repository & PR Code Diff | `640x420` | Header tabs, split diff table, status pills |
| `fw05` | YouTube Watch Player & Up-Next Queue | `640x420` | 16:9 media frame, channel row, right recommendation list |
| `fw06` | New York Times Multi-Column Editorial Front Page | `640x420` | Masthead rules, multi-column headlines & figure wraps |

### 4.2 Suite 3: Liquid Theme Rendering Diff (`lq01`–`lq06`)
| ID | Theme / Glass Surface | Viewport | CPU Raster Parity Notes (`browser_cpu_raster_css_overrides`) |
|---|---|---|---|
| `lq01` | Liquid Dark Theme (`fluid_dark` Aura, Glass Panels & Glow) | `640x420` | Preserves 3-orb radial + 145deg linear dark aura & `rgba(255,255,255,0.22)` top specular border |
| `lq02` | Liquid Light Theme (`fluid_light` Celestial Ether) | `640x420` | Preserves cyan/indigo radial + 155deg light aura & `rgba(255,255,255,0.85)` top specular border |
| `lq03` | macOS Glass Dark Window Gallery (`glass_css.spl`) | `640x420` | Suppresses heavy multi-pass blur & `body::before`/`after` stripes on CPU raster |
| `lq04` | Stitch Glass Obsidian Dark (`glass_obsidian_dark`) | `640x420` | Deep obsidian palette parity with top specular chrome highlight |
| `lq05` | Liquid Frosted `backdrop-filter: blur(12px)` Over Photo & Orbs | `640x420` | Translucent HUD & toast stacking over `sunset.png` and glow orbs |
| `lq06` | UI Kitchen Sink Window (`demo_kitchen_sink.ui.sdn`) | `960x640` | Full hosted GUI comparison under Liquid Glass aura overrides |

### 4.3 Multi-Script Comparison Lanes (`ms01`–`ms04`, `520x340`)
| ID | Scenario | Measured Parity Across `simple_js` / `simple_script` / `agent_script` (`Exact / <=12 / <=32 / MAD`) |
|---|---|---|
| `ms01` | MS01: KPI Card & Status Computation | `0.05% / 88.67% / 93.55% / 6.60` (all 3 script lanes) |
| `ms02` | MS02: Form Fill + Select + Live Preview | `0.05% / 85.04% / 93.65-93.66% / 6.83-6.84` |
| `ms03` | MS03: Kanban State Transition & Column Move | `2.87% / 88.47% / 95.00% / 5.04` |
| `ms04` | MS04: Cooperative Multi-Script Pipeline (JS + Simple + Agent) | `0.08% / 64.18% / 85.48% / 10.78` |
