# WM GUI Window Drawing Feature Expert

## Role

Own feature-specific process knowledge for capture-based verification that the
two WM lanes actually DRAW windows, titlebars, taskbar, and correctly-sized
text: (a) the compositor scene/CSS lane (`os.compositor.wm_scene`) and (b) the
hosted-compositor chrome lane (`os.compositor.host_compositor_entry`). This is
a regression gate for the giant-text "font:" shorthand bug class (CSS weight
parsed as size), not a general WM feature area.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)

## Feature Links

- Driver (probe): [src/os/compositor/wm_gui_window_drawing_evidence.spl](../../../../src/os/compositor/wm_gui_window_drawing_evidence.spl)
  — renders 3 scenes at 1024x768, writes PPM captures, prints per-scene pixel
  metrics (non-background / text-ink "bright" / saturated "accent" counts,
  plus `max_glyph_run_px` — the giant-glyph pathology detector).
- Check script: [scripts/check/check-wm-gui-window-drawing-evidence.shs](../../../../scripts/check/check-wm-gui-window-drawing-evidence.shs)
  — runs the driver, converts each PPM to PNG (`sips`), classifies pass/fail
  per scene, writes `build/wm_gui_window_drawing/report.md`.
- Gate contract spec: [test/03_system/check/wm_gui_window_drawing_spec.spl](../../../../test/03_system/check/wm_gui_window_drawing_spec.spl)
  — pins the script/driver structural contract and the Rust-seed-forbidden
  rejection path (fast, deterministic; does not run the multi-minute render).
- Scene builders exercised: `standard_wm_scene`, `shared_wm_scene_to_chromed_wm_scene`,
  `render_scene_to_backend` in [src/os/compositor/wm_scene.spl](../../../../src/os/compositor/wm_scene.spl).
- Hosted chrome lane exercised: `HostCompositor`, `HeadlessHostCompositorBackend`,
  `render_frame`, `host_chrome_scene_html` in
  [src/os/compositor/host_compositor_entry.spl](../../../../src/os/compositor/host_compositor_entry.spl).
- Underlying CSS/GUI-web renderer (both lanes funnel through this on
  Metal-capable hosts): [src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl](../../../../src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl)
  — owned by a different, adjacent feature area; this gate is a consumer/
  regression check on it, not its owner.
- Related layer expert: [doc/00_llm_process/layer_expert/os_compositor/skill.md](../../layer_expert/os_compositor/skill.md)
- Precedent capture-evidence checks (style/idiom source): `scripts/check/check-hosted-wm-capture-evidence.shs`,
  `scripts/check/check-widget-shells-crossengine-evidence.shs`,
  `src/os/compositor/hosted_wm_capture_evidence.spl`.

## Handoff Notes (2026-07-03)

- **RESOLVED 2026-07-03 — giant-text regression re-landed and fixed**: the
  `wm_scene_css` capture at 1024x768 previously showed "Simple Web WM"
  rendered at ~400-600px/glyph (`max_glyph_run_px=425` vs the <40 floor).
  Root cause: `simple_web_html_layout_renderer.spl` parsed the `font:`
  shorthand with `parse_int(font_norm)`, so `font:600 12px system-ui` yielded
  font-size 600 (weight-as-size), which then flowed to BOTH the software
  painter (`glyph_scale(600)=75`) and the Engine2D fast-lane executor
  (`text_metrics` scale `600/7=85`). The executor / `draw_text` was NOT at
  fault — it already converts px -> cell scale. Commit `70cd415c55` claimed
  the fix but its renderer hunk was lost in a torn commit; it has now been
  RE-LANDED: helper `parse_font_shorthand_size_px` (next to `parse_int_range`,
  "first number attached to px") is called from the `font` shorthand branch
  in `compute_styles`. Probe confirms the WM-scene Draw IR TEXT font-size is
  now 12 (was 600). Resolved bug doc:
  `doc/08_tracking/bug/webengine_font_shorthand_weight_parsed_as_size_2026-07-03.md`.
  Re-run the gate to confirm `giant-glyph-pathology` flips green.
- **LIVE FINDING 2 — chromed-scene render crashes the interpreter**: the
  richer `wm_scene_windows` scene (shared_wm_scene_to_chromed_wm_scene, 3
  windows + taskbar) aborts with `error: semantic: cannot assign to const
  'child_styles'`. Source: `simple_web_html_layout_renderer.spl` ~line 7012
  declares `var child_styles = if <cond>: styles_with_height(...) else:
  styles` and ~line 7063 (flex-stretch branch) reassigns it — the
  interpreter's const tracking treats the `var x = if ...` block binding as
  const at runtime. Only the chromed scene's HTML reaches this flex-stretch
  branch (scene 1 and the host chrome never do). Interpreter bug + any
  renderer-side workaround both live outside this feature's ownership. The
  gate isolates it: each scene renders in its own driver process
  (`WM_GUI_WINDOW_DRAWING_SCENE` env), so this crash fails only its own
  scene (`driver-crashed(exit=1)`) instead of erasing the other captures.
- **Metric design: ink (exact white) vs bright (>210)**: on a correct WM
  render the near-white glass-panel gradients alone measure ~220k "bright"
  pixels with tall vertical runs, so the glyph detector MUST key off exact
  white (255/255/255) — text in both lanes is solid `color:white` /
  `theme.text_primary` bitmap glyphs with no antialiasing, and CSS gradient
  panels never reach 255 on all channels. Do not merge the two classes back.
- **Stale self-hosted binary**: `bin/simple` (release 2026-06-05) aborts on
  `unknown extern function: rt_u32s_from_raw` before rendering — current
  renderer source needs a newer runtime extern. The check script fail-closes
  on this by default; `WM_ALLOW_SEED_DRIVER=1` + explicit `SIMPLE_BIN` is the
  documented opt-in (provenance stamped `rust-seed-opt-in` in evidence +
  report) until a fresh self-hosted binary is deployed.
- **Render cost measured**: `standard_wm_scene` 1024x768 via the engine2d
  fast lane took 243278ms (~4min) under the interpreted seed driver; render
  time >120s is REPORTED (`render_slow`), not failed — a drawing gate should
  not hard-fail on a documented perf finding.
- **Perf gotcha (important for any future edit to this driver or to
  `wm_scene.scene_to_html`)**: `standard_wm_scene`'s `scene_to_html()` embeds
  one giant WM chrome stylesheet (tens of KB, ~47+ CSS rule blocks covering
  every WM surface — command palette, control center, notification center,
  etc.) regardless of how few scene elements are actually present. Under the
  interpreter, a single `render_scene_to_backend()` call therefore costs
  **far longer than pixel count alone would suggest** — a 64x48 (3072px)
  scene took over 3 minutes just from stylesheet parse/cascade cost. Do not
  assume "small canvas = fast render" for this scene family; budget capture
  timeouts (and CI-style gate timeouts) generously (10+ minutes per scene),
  and do not shrink capture resolution as a workaround — the cost is
  stylesheet-bound, not pixel-bound.
- **Interpreter perf gotcha in the driver's own metrics code**: an
  o(w*h) per-pixel measurement pass that calls small helper functions
  (channel-extract, min/max, brightness predicate) per pixel does NOT
  finish inside a 300s budget at 1024x768 (786432 px) — interpreted
  function-call overhead dominates. Fixed by inlining all per-pixel
  arithmetic directly in the loop body (no helper calls, no `y*width+x`
  multiply — a running flat index instead). See `_measure()` in the driver.
  Any future per-pixel analysis added to this driver must stay inlined.
- Metric definitions (`non_bg` / `bright` / `accent` via channel-spread,
  background literal `r=15,g=23,b=42` = `0xFF0F172A` /
  `wm_chrome_theme().compositor_bg`) intentionally mirror
  `scripts/check/validate_hosted_wm_capture_ppm.spl` so this gate's raw
  counts are cross-checkable against the existing hosted-WM capture
  precedent instead of inventing new thresholds from scratch.
- `HeadlessHostCompositorBackend` (in `host_compositor_entry.spl`) is the
  reusable real pixel-capture backend for `HostCompositor` — construct it as
  a local `val`, pass it into `HostCompositor.new(backend, size)`, and read
  `backend.pixels` back after `render_frame()`; do not reuse the test-only
  `CaptureCompositorBackend` from `host_compositor_entry_spec.spl` outside
  that spec (it tracks module-global counters, not a readback pixel buffer).
- Status as of this handoff: gate authored, run end-to-end on the seed
  driver (`WM_ALLOW_SEED_DRIVER=1`), and it correctly FAILS with
  `giant-glyph-pathology` on the CSS-lane scenes while the missing renderer
  fix (above) is un-landed — an intended red. Always read
  `build/wm_gui_window_drawing/report.md` for the latest run's actual
  status/pixel counts; this gate is too slow for a fast pre-commit path.

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area, add or refresh
links here BEFORE committing, so the next agent starts from the current
project state.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
