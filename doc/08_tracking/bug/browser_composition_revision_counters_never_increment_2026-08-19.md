# Hosted browser render-session revision counters never increment

Date: 2026-08-19
Status: OPEN — LIVE (2026-11-11, P3 lane ne2): counter wire-up now present in lib code, but this row's
own specs cannot load on the current seed (nested-call semantic error in the hosted-worker import graph)
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


## Verdict addendum — 2026-11-11 (P3 lane ne2)

Verdict: **LIVE** (status stays OPEN) — with a materially narrowed claim: the
counter wire-up the record said was missing is now present in lib code, but
every spec that could prove it end-to-end currently fails to LOAD on the current
seed, for a different reason.

**Lib code state (read-verified at release/1.0.0 tip):**

- `SimpleWebRenderSession.render()` bumps `composition_revision`
  unconditionally at its tail (`simple_web_render_session.spl:469-471`, right
  after the `paint_count` bump) — no early-return branch skips it; the retained
  path bumps `reuse_count` at `:296-297` when a frame is judged reusable.
- The hosted worker calls `render_session.render(...)` and reads
  `render_session.counters.composition_revision` afterwards
  (`hosted_browser_renderer_worker.spl:208,226`). The "writer unreachable"
  analysis above no longer holds.

**Why this row stays OPEN — its own specs cannot run on this seed.** Both
`test/05_perf/browser/hosted_browser_revision_wire_perf_spec.spl` and the
dedicated integration spec
`test/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.spl`
die at import with:

```
semantic: hosted_browser_revision_wire_perf_spec.spl:15:9: method 'trim' not found
on value of type enum in nested call context
```

The offending pattern is the nested chain `line.slice(...).trim()` in
`src/os/hosted/hosted_browser_renderer_policy.spl` (lines 98, 113, 215, 242,
315, 327-328, 343 — counted this lane), reached through the
`os.hosted.hosted_browser_renderer_worker` import. Reproduced on BOTH
`--mode=interpreter` and the default (JIT) lane; the run never reaches the
behavioral assertion, so the 2026-08-19 failure mode cannot be re-observed or
cleared from this host. The harness additionally reports "light daemon requires
Linux /proc; running directly on windows" — the timing contract needs a
Linux-hosted lane regardless.

This load failure is a tree-side regression in the hosted-worker import graph
(the 2026-08-19 run of the same spec loaded fine), and it blocks every
hosted-worker spec, not just this row's.

**Next step (exact):** apply the documented intermediate-typed-`val` workaround
to `hosted_browser_renderer_policy.spl` (the pattern the 2026-08-15 vulkan lane
recorded for this same seed limitation) or fix the seed nested-call receiver
typing; then run both named specs plus
`hosted_browser_compositor_revision_cache_spec.spl` on a Linux-hosted lane with
the self-hosted binary for honest timing
(`SIMPLE_LIB=src bin/simple test test/05_perf/browser/hosted_browser_revision_wire_perf_spec.spl`).
Lane ne2 did not edit the lib file: normalizing a seed-bug workaround into src/
without owner sign-off is exactly what the project rules warn against; the
seed-level defect deserves its own record.


---

## 2026-11-13 addendum — P3 gpu lane p3-gpu-20261113 (work/p3-gpu-20261113, base 6f4cb189867) — PARTIAL FIX LANDED

**What this lane changed:** applied the documented intermediate-typed-`val`
workaround (the 2026-08-15 vulkan-lane convention for this seed limitation) to the
7 nested `line.slice(...).trim()/to_lower()` chain sites in
`src/os/hosted/hosted_browser_renderer_policy.spl` (all 8 chained expressions:
former lines 98, 113, 215, 242, 315, 327-328, 343). Semantics preserved
(short-circuit `colon > 0` guards restructured to bound-then-test; no behavior
change). Only that file was edited.

**Measured effect (tracked seed `bin/simple.exe`, `SIMPLE_LIB=src`,
`--mode=interpreter --no-cache`, this worktree):**

- The 2026-11-11 load blocker
  (`semantic: hosted_browser_renderer_policy.spl:15:9: method 'trim' not found on
  value of type enum in nested call context`) is **GONE on all three specs**. All
  now compile, load, and execute their examples instead of dying at import:
  - `test/02_integration/rendering/hosted_browser_compositor_revision_cache_spec.spl`
    → 1 executed, 1 failed (was: 0 executed / import error).
  - `test/05_perf/browser/hosted_browser_revision_wire_perf_spec.spl`
    → 1 executed, 1 failed (was: import error).
  - `test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl`
    → 8 executed, 8 failed (was: import error on every example).

**Residual failures — NOT this row's defect, not fixed here:**

1. `hosted_browser_compositor_revision_cache_spec.spl:867` — `class
   BrowserRendererMessage has no field named root_command_request_id`: stale
   spec-vs-class API drift, tracked by
   `browser_ui_specs_stale_or_unlanded_apis_2026-10-31.md` (outside this row's
   list).
2. `hosted_browser_revision_wire_perf_spec.spl` — now fails inside the
   browser-session engine at `method
   _snapshot_current_history_for_departure not found on type object (receiver
   value: BrowserSession(...))` — the same nested-call receiver-typing seed
   limitation, one lane deeper in `src/lib/gc_async_mut/web/` engine code that
   this doc's own 2026-11-11 addendum says is engine-lane owned ("coordinate
   with the in-flight JS-engine work before fixing").
3. Budget/timing assertions in both perf specs still require a Linux-hosted lane
   with the self-hosted binary for honest timing (the 2026-11-11 `/proc`
   limitation stands).

**Verdict: the load-blocking tree-side regression in the hosted-worker import
graph (the exact "Next step" of this record) is FIXED and measured; the row
stays OPEN on the behavioral residual (2) and the timing contract (3).**


---

## 2026-11-13 triage (live-P3 lane l1, work/live-p3-l1-20261113, base f790f7f266e)

**Load-blocker FIXED at this base; row stays OPEN on residuals** — The intermediate-typed-`val` workaround pattern is present in `src/os/hosted/hosted_browser_renderer_policy.spl` (verified by direct read: `val line = raw_line.trim()`, `val name_part = line.slice(...)` + `val name = name_part.trim()`), and the formerly import-blocked specs now compile and execute (this lane's run of the sibling `browser_session_textarea_lifecycle_spec.spl` reaches execution). Residuals unchanged and out of this row's scope: engine-lane nested-call receiver typing one lane deeper, and the Linux-hosted timing contract.
