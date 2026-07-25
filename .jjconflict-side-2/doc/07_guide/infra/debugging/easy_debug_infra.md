# Easy Debug Infrastructure — `std.diag`

**Module:** `src/lib/nogc_sync_mut/diag.spl` · **Import:** `use std.diag.{dbg_stage, ...}`
**Spec:** `test/01_unit/lib/nogc_sync_mut/diag_spec.spl`
**Contract owner:** `doc/05_design/ui/testing/ui_test_infra_design.md` §8.2 — the stderr
line formats below are parsed by UiTest subprocess drivers; do not change them
without updating that design.

Four primitives against four recurring, previously-undiagnosable problem
classes from this repo's real history:

| Problem class | Primitive |
|---|---|
| Silent hangs (browser first-frame hang, hand-added-then-lost stage logs) | stage tracer + cooperative watchdog |
| Quadratic slow paths found only by wall-clock pain (336 KB-CSS, ~6 min/frame) | aggregating timers/counters |
| Silent GPU→software fallbacks / claimed-vs-actual fakery | provenance assert (always-on) |
| Clicks vanishing mid-chain with no visibility | event-chain tracer |

## Enabling — `SIMPLE_DIAG`

```bash
SIMPLE_DIAG=all bin/simple run app.spl                 # everything
SIMPLE_DIAG=stage,watchdog bin/simple run app.spl      # comma list of facets
```

Facets: `stage`, `watchdog`, `timers`, `events`. Read **once** at first use and
cached; when unset, every `dbg_*` call costs one cached bool check — safe to
leave instrumentation in production code. All output goes to **stderr** (stdout
is parsed by gates) and is mirrored through the `lib.log` dispatch so
registered ring/file backends observe diag lines. `dbg_provenance` is
deliberately **not** env-gated.

## The primitives

```simple
use std.diag.{dbg_stage, dbg_deadline, dbg_deadline_clear, dbg_time_begin,
              dbg_time_end, dbg_count, dbg_summary_dump, dbg_event_hop,
              dbg_events_on, dbg_provenance}

# 1. Stage tracer (facet: stage) — one line per call
dbg_stage("browser", "first_frame_start")
#   stderr: [browser] stage first_frame_start +842ms      (delta per component)
dbg_stage_history()   # -> [StageEntry{component, stage, t_ms}], ring cap 256
dbg_stage_dump()      # loud dump of the ring

# 2. Cooperative watchdog (facet: watchdog) — NO threads, interpreter-safe.
#    Breach is detected on the next dbg_stage() call or explicit check.
dbg_deadline("first-frame", 10000)      # arm: must clear within 10s
dbg_deadline_check("first-frame")       # explicit check -> bool (true = breached)
dbg_deadline_clear("first-frame")       # success path: disarm
# Breach fires ONCE, loud, with the recorded stage history:
#   [diag] DEADLINE EXCEEDED first-frame budget=10000ms elapsed=13511ms
#   [diag] recent stage history:
#     [browser] stage parse_html t=...ms
#     [browser] stage css_apply t=...ms

# 3. Aggregating timers/counters (facet: timers) — the quadratic-path finder
dbg_time_begin("css_apply")
# ... work ...
dbg_time_end("css_apply")               # accumulates count/total_ms/max_ms
dbg_count("selector_matches", n)
dbg_summary()        # "css_apply count=180000 total=350000ms max=12ms" per label,
                     # sorted by total descending, plus "counter <label> = N"
dbg_summary_dump()   # emit the summary at exit / session close

# 4. Event-chain tracer (facet: events) — one line per hop
if dbg_events_on():  # guard expensive detail construction in hot loops
    dbg_event_hop("c42", "hit_test", "x=12 y=40 verdict=miss top_widget=none")
#   stderr: [event c42] hit_test x=12 y=40 verdict=miss top_widget=none

# 5. Provenance assert — ALWAYS ON (silent fallbacks are the bug class)
val genuine = dbg_provenance("device_readback", actual_source, "readback")
#   mismatch -> stderr: DIAG-PROVENANCE context=readback claimed=device_readback actual=cpu_mirror
#   returns false on mismatch; also counts (dbg_provenance_mismatches()).
```

## Worked example — diagnosing a first-frame hang

The browser first-frame hang (>5 min, zero output) was only diagnosed after
stage logs were hand-added — and then lost uncommitted. With `std.diag` the
instrumentation is permanent and free when off:

```bash
SIMPLE_DIAG=stage,watchdog bin/simple run src/app/browser/main.spl
```

```simple
# at launch
dbg_deadline("first-frame", 10000)
dbg_stage("browser", "parse_html")
dbg_stage("browser", "css_apply")
dbg_stage("browser", "layout")
dbg_stage("browser", "render_frame_start")
# ... hang happens inside render ...
# on frame present:
dbg_stage("browser", "render_frame_done")
dbg_deadline_clear("first-frame")
```

If the frame never completes, the next `dbg_stage()` anywhere in the process
prints the DEADLINE EXCEEDED block with the history ending at
`render_frame_start` — "hung at render-frame-start" instead of silence. If it
is merely slow, the stage deltas name the slow phase; add
`dbg_time_begin/end("css_apply")` inside the loop and `dbg_summary_dump()` to
see `css_apply count=180000 total=350000ms` — a quadratic path, quantified.

## Test hooks (test-only, documented)

`SIMPLE_DIAG` is cached at first use, so specs cannot toggle it mid-process.
Use `dbg_force_facet("stage"|"watchdog"|"timers"|"events"|"all")` and
`dbg_diag_reset()` (clears all module state) for spec isolation. Assert via
accessors (`dbg_last_emit()`, `dbg_last_breach()`, `dbg_timer_stats(label)`,
`dbg_provenance_mismatches()`), never by reading module globals directly —
interpreter `it` blocks see a stale snapshot of globals.

## Planned integration points — phase 2 (not yet wired)

- **ui.browser stage chain:** `dbg_stage("browser", ...)` at parse/style/layout/
  paint/present + `dbg_deadline("first-frame", 15000)` armed at launch.
- **WM event chain:** `dbg_event_hop(chain_id, ...)` at ingest
  (`WmBridge.handle_input`, winit branch, fake `InputBackend` drain), coordinate
  transform, hit-test verdict, dispatch, handler entry — a vanished click's
  trace ends at the exact hop that dropped it.
- **engine2d readback provenance:** `dbg_provenance(claimed, actual, "readback")`
  at every `read_pixels` consumer and backend resolve (`requested_backend` vs
  `resolved_backend`) — kills the silent GPU→software fallback class.

## Composition notes (no duplicate modules)

- Named `diag` (not `debug`/`dbg`) to avoid colliding with the existing
  interactive debugger modules (`nogc_sync_mut/debug.spl`, `debug/`).
- Emits through `lib.log`'s `log_dispatch_text` (backends) + direct stderr
  (the facade only reaches stderr in panic mode).
- The watchdog composes `std.failsafe.timeout.Deadline` for budgets — no
  second deadline type.
- Interpreter landmines honored (verified in-session): no
  `if val Some(x) = dict.get(k)` (Dict.get returns value-or-nil, the pattern
  never matches); module-global dict writes via `.set()`; globals read through
  accessor functions.
