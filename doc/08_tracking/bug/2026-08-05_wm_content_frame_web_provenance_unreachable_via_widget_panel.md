# `wm_content_frame_web_provenance_valid` is unreachable for `widget-panel`-wrapped WM content

- **Date:** 2026-08-05
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** Medium — the canonical themed WM content-frame path silently
  rejects every frame that goes through it, regardless of caller
- **Area:** `src/lib/common/ui/window_scene.spl` (gate),
  `src/os/compositor/simple_web_window_renderer.spl` (wrapper),
  `src/lib/common/ui/glass_css_components.spl` (`.widget-panel` CSS)

## Summary

`os.compositor.simple_web_window_renderer.simple_web_content_frame_cached` is
the WM's canonical themed content-frame producer. It wraps caller-supplied
`body_html` in a fixed div:

```
<div id='wm-app-content' class='wm-app-content widget-panel'
     data-wm-theme-material-mode='engine2d-cpu-composited-material-v1'
     data-wm-theme-fallback='solid-material' ...>{body_html}</div>
```

The resulting `WmContentFrame` (origin `WM_CONTENT_ORIGIN_SIMPLE_WEB`) is then
gated by `common.ui.window_scene.wm_content_frame_web_provenance_valid`, which
requires `material_fallback_kind` to be one of exactly three combos:
`solid-material` / `cpu-raster-backdrop-sampling-unavailable`,
`cpu-composited-material` / `native-device-backdrop-path-pending`, or
`metal-device-composited-material` / `metal-device-glass-dispatch`.

Two independent facts combine to make this gate **unreachable** for any caller
of the canonical wrapper:

1. In `simple_web_html_layout_renderer_paint_layout.spl`'s per-node style
   computation, the `solid-material` fallback kind is only assigned when
   `data-wm-theme-material-mode` is **absent** (`material_mode_attr == ""`).
   The wrapper div always sets it, so that branch can never fire for
   wrapper-produced content — the only reachable non-`"none"` kind is
   `cpu-composited-material`, which requires `material_ready == true`.
2. `material_ready` requires `backdrop.admitted`, which requires
   `st.backdrop_filter_raw` to parse as the **exact** two-space-separated-term
   form `blur(Npx) saturate(M%)` (`simple_web_backdrop_admission` in
   `simple_web_html_layout_renderer_foundation.spl`, whole-string round-trip
   checked). The wrapper's own `.widget-panel` class — applied unconditionally
   — declares `backdrop-filter: blur(var(--glass-blur-surface));` in
   `glass_css_components.spl`: **one** term, no `saturate(...)`. Admission
   therefore always fails for wrapper-produced content, independent of the
   caller's `body_html`.

Net effect: `material_fallback_kind` stays at its struct default (`"none"`)
for any content rendered through the canonical wrapper, so
`wm_content_frame_web_provenance_valid` returns `false` and
`HostCompositor.set_external_web_frame` rejects the frame every time,
regardless of what HTML the caller supplies.

Scanning `glass_css_components.spl`, 17 of 21 `backdrop-filter:` declarations
are the same one-term `blur(...)` form; 4 are a three-term
`blur(...) saturate(...) brightness(...)` form (also rejected — the parser
requires exactly 2 terms). Only `.surface-1`..`.surface-4`, `.glass`, and a
few shell components (`glass_css_surfaces.spl`, `glass_css_shell.spl`) use the
admitted two-term `blur(Npx) saturate(M%)` form with literal px/percent
values. None of those classes are applied by the WM content wrapper.

## Reproduction

`src/app/wm_showcase/_probe_web_frame.spl` (throwaway probe, not committed)
built a frame via `simple_web_content_frame_cached` with a themed 3-element
body and printed:

```
engine2d_status=engine2d_rendered
engine2d_backend=qualcomm
material_fallback_kind=none
material_fallback_reason=not_requested
provenance_valid=false
```

`engine2d_status=engine2d_rendered` confirms the render itself succeeded (not
a budget-timeout or backend failure) — the rejection is purely the material
provenance gate.

## Discovered via

`test/03_system/gui/wm_showcase_session_capture_spec.spl` /
`src/app/wm_showcase/` (WM showcase). The showcase's web-render window
originally used `simple_web_content_frame_cached`; every open was rejected
with `web-frame-provenance-rejected`, which also silently starved the
sabotage-restore assertion (`web_reopened` stayed `false` since
`set_external_web_frame` never returned `true`). Worked around in the
showcase by rendering the web window's HTML through the same ungated
`simple_web_render_html_to_readback_result_with_engine2d_backend` +
`wm_gui_content_frame_from_pixels` path the GUI window already uses (see
`src/app/wm_showcase/session.spl` header comment, "Web window producer
note"). That sidesteps the gate rather than fixing it — the showcase does not
exercise `simple_web_content_frame_cached`'s themed WM-material contract at
all.

## Suggested fix (not attempted here — out of showcase scope)

Either (a) give `.widget-panel` a two-term `blur(Npx) saturate(M%)` backdrop
declaration matching the `.surface-N` convention, or (b) widen
`simple_web_backdrop_admission` to accept a blur-only declaration (CSS itself
does not require `saturate` alongside `backdrop-filter: blur(...)`) defaulting
`realized_saturation_milli` to 100%, or (c) change the wrapper to apply one of
the already-admitted surface classes instead of `.widget-panel`. Any of these
touches shared theme/renderer code used well beyond this showcase and needs
its own verification pass; each interpreted HTML render in this environment
costs 30-50 CPU-minutes, so iterating on it is expensive.
