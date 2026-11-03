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

## 2026-11-03 source repair candidate (not qualified)

The current first faulty boundary is the shell, rather than the compositor's
already distinct content-kind branches. `DesktopShell.run` now requires the
caller-owned `Engine2dWmFrameExecutor`, retains its WM/input/pointer/shortcut/
process-reconciliation sequence, and calls `render_baremetal_frame` instead of
the direct `render_all` compatibility route. There are no OS callers of the old
zero-argument `run` in the inspected release source. New callers must supply
the real backend/framebuffer executor; this change does not manufacture a
software executor for them.

`render_baremetal_frame` now always obtains the GUI/Web/pixel frames for its
scene revision. The global `_WM_CONTENT_FRAMES_ENABLED = false` bypass is
removed. A failed executor result still leaves successful shell revisions
unchanged. Existing production `run_baremetal` callers retain their supplied
executor and presentation owner.

New regression: `test/01_unit/os/compositor/wm_shell_content_dispatch_spec.spl`
contains six scenarios: mixed canonical producer kinds and dimensions; actual
shared-executor pixel readback; GUI pointer action/frame revisions; empty,
unknown and minimized content exclusion; failed-executor revision retention;
and the legacy-loop source-routing contract. The earlier compatibility probe
is preserved but cannot qualify the canonical shell path.

**TEST_BLOCKED / UNRUN:** `bin/release` is absent on this Windows host. The
tracked `bin/simple.exe` is a Rust bootstrap seed and is not an admitted test
producer. No behavioral scenario or native/QEMU frame gate has passed here.
Run the new spec with an admitted self-hosted CLI, followed by the real
SimpleOS frame/provenance gate using its caller-owned framebuffer executor.

The removed W1 workaround historically suppressed an
`rt_string_concat`/`memcpy` page fault in
`_engine2d_draw_ir_render_glass_material` (2026-08-10 investigation). Removing
the content bypass does not establish that fault is repaired; a current guest
must render and present nonempty content successfully before qualification.
Keep this bug open pending that evidence. Hosted remote GUI-frame production
remains a separate unresolved owner boundary; no universal BrowserRenderer
route is accepted as proof of GUI dispatch.
