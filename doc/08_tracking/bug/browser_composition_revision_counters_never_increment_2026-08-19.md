# Hosted browser render-session revision counters never increment

Date: 2026-08-19
Status: OPEN
Found by: `test/05_perf/browser/hosted_browser_revision_wire_perf_spec.spl`,
`test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl`

## Symptom

Both specs now LOAD and RUN to completion (the stale
`BrowserRendererMessage` -> `BrowserRendererCapabilityMessage` call shape and
the missing `browser_session_loading` import in the worker module graph are
fixed). What remains is a behaviour gap, not a load failure:

```
hosted_revision_wire_perf pairs=11 viewport=64x64 changed_p50_ns=107686572 unchanged_p50_ns=106791269 ratio_x1000=991 render_count=26 reuse_count=0
  ✗ keeps unchanged response routing faster than changed frames
    expected 0 to equal 14
Results: 1 total, 0 passed, 1 failed
```

`expect(after.composition_revision).to_equal(before_composition_revision + WIRE_TIMED_PAIRS)`
sees `0` where `14` is required, and the printed evidence shows
`render_count=26 reuse_count=0` where the contract is `render_count=12`,
`reuse_count=14`.

Production-budget spec fails the same way, as
`expected subject to be truthy, got 0` on `worker.handle(...).ok`.

## Analysis

`worker.render_session.counters.composition_revision` stays `0` for the whole
run. `src/os/hosted/hosted_browser_renderer_worker.spl` only READS it
(lines 223, 270, 308); nothing on the reachable path bumps it. The
revision-reuse fast path in
`Engine2dCompositorBackend.render_draw_ir_composition_resources_revision`
therefore never observes an unchanged revision and re-renders every frame
(`revision_reuse_count == 0`).

The pixels are correct (`mismatches == 0`), so this is a missing
revision/reuse accounting wire-up, not a rendering defect.

## Not yet done

Locate the intended writer of `counters.composition_revision` /
`counters.reuse_count` in the render-session pipeline and wire it, then
re-run both specs.

## Narrowing done

`SimpleWebRenderSession` is a `class` (line 191 of
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_render_session.spl`), so
`self.render_session` passed into the free function `_worker_frame` is shared
by reference -- this is NOT a value-copy loss.

The writer exists and is reachable in principle:
`simple_web_render_session.spl:469-470` bumps `composition_revision` (right
after `paint_count`) inside `render()`, and `:296` bumps `reuse_count`.
Since the test observes BOTH at `0` while pixels are correct, the frame path
the hosted worker takes is not the `render()` body that carries these bumps.
Next step is to instrument which branch of `_worker_frame` /
`SimpleWebRenderSession.render` the hosted worker actually executes.
