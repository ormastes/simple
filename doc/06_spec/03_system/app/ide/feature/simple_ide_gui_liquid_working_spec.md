# Simple IDE GUI Liquid Glass Working Verification

> Verifies the Pure-Simple IDE GUI pipeline (`ide_feature_check_report`, `ide_gui_sanity_summary`, `ide_interaction_evidence`, `ide_render_gui_frame`, and `gui_shell_render_frame`) alongside Pure-Simple Web Liquid Glass rendering and the `1380x860` sRGB Electron Liquid Glass IDE shell.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple IDE GUI Liquid Glass Working Verification

Verifies the Simple IDE GUI stack end-to-end across Pure-Simple software Engine2D rendering, `gui_shell_render_frame` HTML composition + Web layout rasterization, and the Electron Liquid Glass IDE shell.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Source | `test/03_system/app/ide/feature/simple_ide_gui_liquid_working_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the Simple IDE GUI stack end-to-end without placeholders:

1. Production feature report (`ide_feature_check_report("gui")`), GUI sanity summary (`ide_gui_sanity_summary()`), and live editor/Office interaction evidence (`ide_interaction_evidence("gui", ...)`).
2. Real software Engine2D IDE frame rendering (`ide_render_gui_frame`) with `.spl` files opened in `EditSession` and PNG RGB encoding (`encode_argb_to_png_rgb`).
3. HTML shell frame rendering (`gui_shell_render_frame`) including document tab and file-tree rendering, custom-editor status reporting, and Pure-Simple web Liquid Glass software pixel rasterization (`simple_web_layout_render_html_software_pixels_with_images`).
4. Electron Liquid Glass IDE GUI shell artifacts (`tools/electron-shell/simple_ide_gui_app.js` and `tools/electron-shell/simple_ide_gui_shell.html`).

## Evidence

Display policy: `links`

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `ide_engine2d_frame.png` | PNG capture | `build/test-artifacts/03_system/app/ide/feature/simple_ide_gui_liquid_working/ide_engine2d_frame.png` |

## Scenarios

### REQ-IDE-GUI-LIQUID-001 Simple IDE GUI Liquid Glass verification

#### verifies IDE GUI sanity, interaction evidence, Engine2D and Web Liquid rendering, and Electron shell

- Run production IDE feature report, GUI sanity summary, and interaction evidence
   - Expected: `report_lines.len()` is greater than `10` and contains `gui-backend:`
   - Expected: `gui_summary` contains `gui-backend:` and `md=true`
   - Expected: `ide_gui_bounds_valid()` is `true`
   - Expected: `ev.opened` and `ev.edited` are `true`, `ev.diagnostic_count` equals `0`, `ev.office_component` equals `sheets`, and `ide_interaction_exit_code(ev)` equals `0`
- Render software Engine2D IDE frame with real Simple sources and encode PNG
   - GUI capture: after_step (`1120x720` software Engine2D IDE frame encoded via `encode_argb_to_png_rgb`)
   - Expected: `e2d_frame.width` equals `1120`, `e2d_frame.height` equals `720`, `e2d_frame.resolved_backend` equals `software`, `e2d_frame.pixels.len()` equals `806400`, `e2d_frame.checksum` is greater than `0`, and `e2d_frame.active_file` equals `main.spl`
   - Expected: encoded PNG begins with signature `[137u8, 80u8, 78u8, 71u8]` and writes cleanly
- Verify `gui_shell_render_frame` populates tabs and tree and renders Liquid Glass web pixels
   - Expected: `gf.tab_bar_html` contains `main.spl` and `gui_shell_render.spl`
   - Expected: `gf.file_tree_html` contains `main.spl`
   - Expected: `gf.editor_html` contains `editor-area` and `problems-pane`
   - Expected: `web_px.len()` equals `33600` for `240x140` Liquid Glass web frame
- Verify Electron Simple IDE Liquid Glass shell files and contracts
   - Expected: `tools/electron-shell/simple_ide_gui_app.js` and `tools/electron-shell/simple_ide_gui_shell.html` exist
   - Expected: `app_js` configures `1380`x`860`, `force-color-profile` sRGB, and logs `[simple-ide-gui] ready`
   - Expected: `shell_html` provides `fluid_dark`, `glass_obsidian_dark`, and `fluid_light` themes and embeds `ide_engine2d_frame.png` & `ide_web_liquid_frame.png`

</details>
