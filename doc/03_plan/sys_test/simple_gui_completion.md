# Simple GUI Completion — System Test Plan (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Plan Complete
- **Target Branch:** `release/1.0.0`
- **Requirements:** `doc/02_requirements/feature/simple_gui_completion.md`, `doc/02_requirements/nfr/simple_gui_completion.md`

---

## 1. Execution Constraints

- Run **at most one single-file `bin/simple test --no-session-daemon <spec>`** at a time (sequential execution; no parallel test batches, no `native-build` while P4 build runs).
- All SSpec matchers use built-ins only (`to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`).
- Zero `.spl` files permitted under `doc/06_spec` (`find doc/06_spec -name '*_spec.spl' | wc -l == 0`).
- Zero silent skipped assertions: environment-dependent hardware/macOS checks must emit explicit structured skip receipts or pass end-to-end.

---

## 2. Requirement-to-Spec Traceability Matrix

| Req ID | NFR IDs | Spec File(s) | Key Assertions |
|---|---|---|---|
| `REQ-SGUI-001` | `NFR-SGUI-004`, `NFR-SGUI-005` | `test/01_unit/app/ui/async_default_api_spec.spl`, `test/01_unit/app/ui/unified_app_spec.spl`, `test/03_system/gui/capability_negotiation_spec.spl`, `test/03_system/gui/unified_app_spec.spl` | All 4 specs resolve canonical `app.ui.backend_factory` / `app.ui.none.app` / `nogc_sync_mut.ui.session` imports and execute >0 assertions; `RenderBackend` & `ScreenHost` contracts pass `simple check`. |
| `REQ-SGUI-002` | `NFR-SGUI-002` | `test/01_unit/lib/tiny/gui_sibling_flow_bounds_spec.spl`, `test/01_unit/lib/tiny/tiny_layout_linear_spec.spl` | Saturating i32 sibling offsets + `metadata_valid()` returns `false` after same-length in-place `bounds` or `parent` edits; O(1) scan steps preserved when unmutated. |
| `REQ-SGUI-003` | `NFR-SGUI-005` | `test/01_unit/app/ui/web_wm_modern_shell_spec.spl`, `test/01_unit/lib/common/ui/theme_package_spec.spl`, `test/02_integration/app/ui_log_modes_spec.spl`, `test/01_unit/lib/common/ui/wm_full_stack_demo_child_theme_spec.spl` | Cascade-winning `--ui-bg` / `--ui-accent` read accurately; `src/app/ui/main.spl --help` builds/runs; `set_external_child_frame` rejects mismatched `theme_id`. |
| `REQ-SGUI-004` | `NFR-SGUI-002` | `test/01_unit/lib/common/ui/focus_tab_index_spec.spl` | `get_focusable_ordered` excludes panels/labels/disabled/hidden nodes; `FocusEvent(_, "blur")` clears `focused_id` and `ui_focus`/`preedit`. |
| `REQ-SGUI-005` | `NFR-SGUI-002` | `test/01_unit/lib/common/ui/widget_hit_spec.spl`, `test/01_unit/lib/common/ui/widget_text_edit_spec.spl`, `test/01_unit/lib/common/ui/showcase_core_spec.spl`, `test/03_system/ui_showcase/showcase_hosts_spec.spl` | Pointer capture completes click only on release inside captured control; `GUI_EVT_TEXT_INPUT` & `GUI_EVT_KEYBOARD` shift modifiers route to `HostInputEvent.Key`. |
| `REQ-SGUI-006` | `NFR-SGUI-003` | `test/01_unit/app/ui_showcase/host_gui_device_scale_spec.spl` | `GUI_EVT_SCALE_CHANGED` updates `ScreenGuiHost.scale`, `w/h`, `dev_w/dev_h`, invalidates `retained_pixels`, and emits `HostInputEvent.Resize`. |
| `REQ-SGUI-007` | `NFR-SGUI-001` | `test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl`, `test/01_unit/os/compositor/wm_retained_parent_sampling_damage_spec.spl`, `test/01_unit/os/compositor/wm_retained_clock_tick_spec.spl`, `test/02_integration/rendering/engine2d_wm_local_lane_clock_tick_spec.spl` | `GuiRetainedRenderSession.render_damage` handles local damage over parent-sampling glass root; `Engine2dWmFrameExecutor` clock ticks stay local with full-frame pixel parity. |
| `REQ-SGUI-008` | `NFR-SGUI-002`, `NFR-SGUI-004` | `test/01_unit/lib/common/ui/showcase_core_spec.spl`, `test/03_system/ui_showcase/showcase_hosts_spec.spl`, `test/03_system/gui/showcase_event_spec.spl` | All `ScreenHost` targets produce non-blank `DrawIrV3Scene` frames with prefix isolation. |
| `REQ-SGUI-009` | `NFR-SGUI-004` | `test/03_system/gui/macos_gui_live_window_evidence_spec.spl`, `test/03_system/gui/ui_draw_ir_pipeline_spec.spl`, `test/03_system/gui/engine2d_gpu_offload_contract_spec.spl` | Live macOS `SimpleGui` window capture + `DrawIrV3Scene` / Engine2D contract specs pass on non-seed binary. |
| `REQ-SGUI-010` | `NFR-SGUI-002` | `test/03_system/wm/wm_full_stack_demo_spec.spl` | All examples (6/6) pass including titlebar drag, minimize, maximize/restore, resize, and taskbar restore. |

---

## 3. Static Verification & Audit Gate

1. `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` -> exit `0`
2. `find doc/06_spec -name '*_spec.spl' | wc -l` -> `0`
3. `<simple_bin> check` on modified modules under `src/lib/common/ui`, `src/lib/nogc_sync_mut/ui`, `src/lib/nogc_sync_mut/tiny/gui`, `src/lib/gc_async_mut/ui`, `src/app/ui_showcase`, `src/app/ui.web`, `src/os/compositor` -> exit `0`
4. Sequential single-file `<simple_bin> test --no-session-daemon <spec>` runs across all specs in Section 2.

---

## 4. Chrome Base vs Pure-Simple Base & Multi-Variation Comparison App

In addition to unit/system SSpec gates, GUI and hosted UI parity against Chrome (`Blink/Skia`) is verified visually and pixel-quantitatively through the in-tree comparison pipeline (`src/app/html_layout_compare/main.spl`, `examples/browser/html_layout_compare/variations.sdn`, and `tools/electron-shell/html_layout_compare_app.js`):

### 4.1 Scope & Variations (`v01`–`v14`)
- **HTML/CSS/Text/Image Variations (`v01`–`v12`, `520x340`):** Flexbox hero/cards (`v01`), left/right floats (`v02`), CSS Grid 3x2 (`v03`), 3-column workspace shell (`v04`), media thread (`v05`), `object-fit` matrix (`v06`), data tables with `colspan` (`v07`), positioned overlays & `z-index` (`v08`), inline typography & alignment (`v09`), `flex-wrap` chips/cards (`v10`), form controls (`v11`), and 2-column lists/blockquotes (`v12`).
- **Full Browser Showcase (`v13`, `640x420`):** `examples/06_io/ui/browser_common_elements_showcase.html` full standards showcase parity.
- **Full GUI Kitchen Sink Window (`v14`, `960x640`):** `examples/06_io/ui/demo_kitchen_sink.ui.sdn` rendered across Chrome (`capture_after_chrome_960x640.png`) vs Pure-Simple headless/GUI window (`6.66%` exact, `53.27%` `<=12px`, `84.16%` `<=32px`, `18.27` MAD in the macOS reference bundle).

### 4.2 Interactive JS / SimpleScript & Event Cases (`e01`–`e06`)
| Event Case | Interaction Surface | Expected Chrome vs Pure-Simple Parity |
|---|---|---|
| `e01` | Click Button & Action Dispatch | DOM/widget click updates target active visual fill and action receipt. |
| `e02` | Pointer Move & Drag Capture | Window/widget drag tracks outside bounds cleanly (`ui_captured_id`) and ignores sibling release. |
| `e03` | Dropdown `<select>` & `<details>` Toggle | Popup open state and selected value match across post-toggle captures. |
| `e04` | Keyboard Input, Shift & Focus Traversal | `Tab` / `FocusNext` skips disabled/hidden/static nodes, preserves Shift glyphs, and clears `preedit` on blur. |
| `e05` | Wheel Scroll Clamping & Linked Sync | Wheel delta clamps `scroll_y` cleanly and keeps linked panels synchronized. |
| `e06` | JS / SimpleScript DOM Mutation & Re-render | Script listener mutates DOM once per revision and matches post-event repaint. |

### 4.3 Backend Provenance Titles & Launch / Verify Commands
- Every comparison pane displays explicit provenance titles (`Chrome (Blink / Skia)` vs `Pure-Simple Web (engine=pure_simple)` vs `4x |Chrome - Simple Web| Diff`) so no fallback capture can masquerade as native parity.
- **Render & write SDN report (`compare_report.sdn`):**
  ```sh
  SIMPLE_LIB=src bin/simple run src/app/html_layout_compare/main.spl --out-dir build/html_layout_compare
  ```
- **Capture Chrome reference PNGs & export Electron manifest (`--json`):**
  ```sh
  npx electron tools/electron-shell/html_layout_compare_app.js --capture-chrome build/html_layout_compare --pages examples/browser/html_layout_compare/pages
  SIMPLE_LIB=src bin/simple run src/app/html_layout_compare/main.spl --out-dir build/html_layout_compare --json
  ```
- **Launch interactive `1440x920` 4-tab Compare Studio:**
  ```sh
  npx electron tools/electron-shell/html_layout_compare_app.js --dir build/html_layout_compare
  ```
- **SPipe system test gate:**
  ```sh
  SIMPLE_LIB=src bin/simple test test/03_system/app/simple_web/feature/chrome_vs_simple_web_layout_compare_spec.spl --mode=interpreter --memory-limit=1G
  ```
