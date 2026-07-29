# WM content-kind render runtime gate

Status: RED — focused probe exists; no admitted native execution yet.

## Current source truth

The original universal Simple Web fallback is gone. `WindowSurface` owns a
scalar `content_kind` and generation handle. `Compositor.render_all()` has
separate GUI, Web, and pixel branches, while the SimpleOS baremetal shell
produces all three as `WmContentFrame` values for the shared Engine2D executor.

Two gaps remain:

- legacy `DesktopShell.run()` still calls the direct `render_all()` compatibility
  path instead of the shared frame executor;
- the hosted compositor accepts generic external content frames, but its live
  hosted entry creates BrowserRenderer frames for every remote-owned window and
  has no live GUI-frame producer.

## Focused runtime gate

`test/fixtures/wm_compositor_content_kind_render_probe.spl` creates nonoverlapping
GUI, Web, and pixel windows, invokes the real `Compositor.render_all()`, checks
each body against its canonical producer, then checks GUI and pixel handle
counts return to baseline after close.

The no-stub pure-Simple Stage-2 build compiled the closure but the
`core-c-bootstrap` capsule failed closed at link because it intentionally lacks
Web/GPU/SQLite runtime symbols. No `simple-core` archive is installed. The
bounded Cranelift attempt produced no artifact before timeout and was stopped.
No stub fallback or Rust seed result is accepted as evidence.

## Next action

Provide the supported pure-Simple `simple-core` runtime archive or narrow the
GUI/Web renderer closure so the focused probe links against the admitted core
capsule. Then run the probe unchanged before altering production routing.
