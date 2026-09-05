# WM scenes through the web-render lane compose visually scrambled layout

- **Status:** LARGELY RESOLVED 2026-07-03 — "scrambled" was translucency, not layout.
  Chrome ground-truth render of the same HTML proved geometry was correct all
  along. Two-part fix landed: (1) renderer parses solid `background`/
  `background-color` rgba() alpha-aware and composites via blend_opacity
  (software lane); (2) Metal MSL `kernel_draw_rect_filled` now does Porter-Duff
  src-over bit-identical to the CPU `blend()` (engine2d lane; parity harness
  `rect_blend` scene pins it, 0 mismatches). wm_scene_windows capture after:
  ink 369k→32k px, max_glyph_run 295→13 (with the stroke-narrow glyph
  discriminator in the evidence driver). RESIDUAL (still open below):
  backdrop-filter blur is unimplemented, so translucent window glass reveals
  sharp detail beneath instead of Chrome's frosted look; host_compositor lane
  render still exceeds the gate timeout (per-window full CSS render per frame).
- **Date:** 2026-07-03
- **Severity:** high for WM-on-web production readiness (text sizing itself is fixed)
- **Evidence:** `build/wm_gui_window_drawing/wm_scene_css.png`, `build/wm_gui_window_drawing/wm_scene_windows.png` (gate: `scripts/check/check-wm-gui-window-drawing-evidence.shs`)

## Findings (capture-verified, driver with CONST_NAMES fix, 1024x768)

1. `wm_scene_css` (standard_wm_scene): renders as one flat blue field with a
   topbar strip + "workspace" chip. The scene's windows / taskbar / launcher
   elements are not visible as distinct surfaces (either covered by a
   full-viewport surface, positioned off-view, or their absolute geometry is
   lost during CSS cascade/layout). Pixel floors pass (non_bg/ink/accent) —
   they count classes of pixels, not structure, so this scene is a
   false-comfort pass.
2. `wm_scene_windows` (shared_wm_scene_to_chromed_wm_scene, 3 windows +
   taskbar): now renders end-to-end (previously crashed on the interpreter
   CONST_NAMES bug, fixed in `interp_const_names_branch_val_poisons_var_2026-07-03.md`),
   render 634s. Small text is correctly sized and readable (Cancel/Block/
   Terminal/win-1/win-3/09:41 etc.), taskbar strip present at bottom — but
   window frames are NOT composed as coherent rectangles: content fragments
   scattered and overlapping across the canvas, large bare exact-white panels,
   big unpainted dark regions.
3. Gate metric gap: `max_glyph_run_px` keys on exact-white pixels assuming
   "text ink is exact white, panels are near-white". The chromed scene paints
   exact-white content panels, so vertical runs hit 222px and trip the <40
   giant-glyph floor without any giant text. Detector needs a
   structure-aware refinement (e.g. cap run width, or require dark
   neighborhood) before it is meaningful on scenes with white surfaces.

## Suspected root

Same CSS layout divergence family being worked in the cross-engine parity
lane (`doc/08_tracking/bug/simple_web_widget_css_divergence_vs_chromium_2026-07-03.md`):
absolute-position/containing-block and flex composition errors scramble
`scene_to_html()` output. Re-run this gate after the parity fixes land; then
split whatever remains into scene-HTML vs renderer bugs.
