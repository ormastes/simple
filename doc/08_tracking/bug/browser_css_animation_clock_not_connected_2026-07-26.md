# Browser CSS animation clock is not connected

## Status

Frame sampling and the hosted compositor invalidation path are wired;
target-binary evidence and non-hosted browser surfaces remain open.

## Evidence

- `extract_keyframes()` builds a `KeyframeRegistry`, but production style
  processing discarded that registry.
- `AnimationEngine` and `AnimationController` have no production callers.
- `Animation` previously had no target node and emitted every keyframe update
  for node `0`. It now carries `node_id`; `create_for_node` and interpolation
  preserve that identity. `Transition` uses the same target-aware contract
  instead of emitting node-zero updates.
- `AnimationEngine` now caps animations and transitions at 1024 each and
  emitted style updates at 4096 per tick, bounding retained state and frame
  work before production wiring.
- Keyframe declarations now parse into typed color, pixel-length, percentage,
  and numeric values, and midpoint sampling has focused coverage. Color
  interpolation includes alpha. This fixes the value path but does not supply
  the missing production clock.
- `BrowserSession.advance_time()` now supplies the same monotonic document
  clock to CSS keyframe sampling and JavaScript timers/rAF.
- No production `src/**` host currently calls `BrowserSession.advance_time()`
  or requests repaint for CSS-only animation. The current fixture drives time
  and rendering manually, so it proves sampled frames but not autonomous
  production animation scheduling.
- The Engine2D bridge previously imported and called
  `simple_web_layout_render_html_pixels_engine2d_at_time()` without any
  definition, so the authored animation fixture could not compile through the
  target path. The layout/Draw IR and fast Engine2D at-time functions now exist
  and sample bounded keyframes before layout.

The discarded registry parse was removed because it consumed hostile-page CPU
without affecting rendering.

## Required fix

The layout style owner now samples bounded keyframes from computed
`animation-*` properties before Draw IR lowering. BrowserSession resets the
animation epoch on navigation and supplies elapsed monotonic time to the
Engine2D render path.

The hosted compositor now evaluates animation lifetime once per content
revision, bypasses its static pixel cache only for animated content, renders
against a content-local epoch, and dirties visible animated windows on a
bounded 16ms cadence. Finite animations schedule their exact final frame and
then become quiescent; minimized windows do not request frames.

The 2026-07-27 mainline repair also removed accidentally committed jj conflict
blocks from the at-time renderer/Engine2D chain and restored the animation-aware
methods on the shared pixel cache. The compositor regression covers red start,
distinct midpoint, blue endpoint, cadence, and quiescence.

Other production surfaces that bypass both BrowserSession and the hosted
compositor still need an equivalent host-owned clock contract. In particular,
the stdin-driven Electron browser example has no frame IPC.

## Required evidence

The production fixture and integration spec now require distinct
start/mid/end frames from CSS `@keyframes` without JavaScript mutating the
animated property. They cannot be executed until the separately recorded
target compiler build failure is fixed; no runtime PASS is claimed.
