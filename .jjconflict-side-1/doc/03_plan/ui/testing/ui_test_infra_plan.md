# UI Test Infrastructure — Implementation Plan

**Date:** 2026-07-05
**Design:** `doc/05_design/ui/testing/ui_test_infra_design.md`
**Research:** `doc/01_research/ui/testing/ui_test_infra_research.md`

## Status / honesty

- This is a **plan** — none of the phases below are implemented. Everything
  the phases build ON exists and is file:line-verified in the research doc.
- Phases are sized for delegation to Sonnet agents (~1 agent-day each),
  independently landable on `main` (no branches), each with its own spec
  tests + evidence gate. Order matters only where stated (P0 → P1 → others;
  P5 needs P2 or P3 for a real consumer).
- A **P0 implementation agent is being started in parallel** from the same
  primitive list as design §8. P0 below documents the expected contract;
  conflicts found during research are flagged in §P0-conflicts.
- Every phase must run on the deployed pure-Simple binary
  (`bin/release/<triple>/simple`), with `SIMPLE_EXECUTION_MODE=interpret`
  for anything touching winit (filed JIT bug).

## Cross-phase conventions

- Specs: `test/03_system/ui_test/<area>/*_spec.spl`, Modern SSpec style
  (`.claude/templates/spipe_template.spl`), `# @cover` on system specs.
- Evidence: one `scripts/check/check-ui-test-<area>-evidence.shs` per phase,
  emitting flat `evidence.env` keys `ui_test_<area>_status=pass|fail` plus
  phase-specific keys; final shell test is the gate (63-gate conventions).
  Gates must grep spec output for `✗` (interpreter runner verifies loading,
  not it-block execution).
- Commit per landed fix; refresh the related LLM wiki entries
  (`doc/00_llm_process/feature_expert/…`, `layer_expert/…`) in the same
  change (vcs rule).

---

## P0 — std.diag debug primitives (parallel agent; contract here)

> **Status (2026-07-05): IMPLEMENTED** at `src/lib/nogc_sync_mut/diag.spl`
> (commit `70a5af4b`), 13/13 specs green in
> `test/01_unit/lib/nogc_sync_mut/diag_spec.spl`. P1-P6 below are unchanged
> (not yet implemented).

**Goal:** land the shared debug primitives the test infra consumes
(design §8): stage tracer, cooperative watchdog, aggregating
timers/counters, event-chain tracer, provenance assert.

**Files to create:**
- `src/lib/nogc_sync_mut/diag.spl` — the module (single file).
- Re-export shims: `src/lib/nogc_async_mut/diag.spl`,
  `src/lib/gc_async_mut/diag.spl`, `src/lib/gc_sync_mut/diag.spl`
  (1-line, following the `log.spl` shim chain).
- `test/unit/lib/diag_spec.spl`.

**Contract (must match design §8.2 exactly — P1+ depends on it):**
- API: `dbg_stage(component, stage)`, `dbg_stage_history() -> [StageEntry]`,
  `dbg_stage_dump()`, `dbg_deadline(label, budget_ms)`,
  `dbg_deadline_check(label) -> bool` (auto-checked inside `dbg_stage`),
  `dbg_deadline_clear(label)`, `dbg_time_begin/dbg_time_end(label)`,
  `dbg_count(label, delta)`, `dbg_summary() -> text`, `dbg_summary_dump()`,
  `dbg_event_hop(chain_id, hop, detail)`, `dbg_events_on() -> bool`,
  `dbg_provenance(claimed, actual, context)`.
- Env: `SIMPLE_DIAG` = `all` | comma list of `stage,watchdog,timers,events`,
  read once at module load (zero-cost off, `log.spl` pattern);
  `SIMPLE_DIAG_FILE` optional sink. `dbg_provenance` mismatch warning is
  ALWAYS on.
- Stderr formats (parsed by P2's subprocess driver — stable):
  `[<component>] stage <stage> +<delta_ms>ms` and
  `[event <chain_id>] <hop> <detail>` and
  `DIAG-PROVENANCE context=<c> claimed=<x> actual=<y>`.
- Ring cap 256; watchdog is cooperative (no threads), interpreter-safe.
- Compose, don't duplicate: emit via `nogc_sync_mut/log.spl` facade
  (`_emit:113` path); deadlines via `failsafe/timeout.spl` `Deadline:109`;
  do NOT name the module `dbg`/`debug` (collides with
  `nogc_sync_mut/debug.spl`/`debugger.spl`).
- First instrumentation (same phase, proves the primitives):
  `src/app/ui.browser/app.spl`/`backend.spl` stage points (the bug-doc
  sequence args-parsed → first-frame-drawn,
  `browser_engine_css_size_quadratic_pixel_render_2026-07-04.md:214-222`;
  replaces the stale comment at `ui.browser/main.spl:76-77`),
  `src/os/hosted/hosted_entry.spl` (args-parsed / window-created /
  first-frame-drawn), compositor frame loop (`compositor.spl:343` area:
  render-frame-start / frame-presented).

**Specs:** gating on/off (off = no output, no ring growth); stage delta
math; deadline breach dumps history exactly once; timer aggregation
count/total/max; provenance always-on; format stability (string-compare the
emitted lines).
**Evidence:** `check-ui-test-diag-evidence.shs` — run an instrumented
`ui.browser` open under `SIMPLE_DIAG=all`, assert the full stage sequence
appears in order with monotonic deltas; run once with a 1 ms deadline and
assert the breach block appears once.
**Risks:** hot-loop cost (must be one bool test when off — verify frame time
before/after per repo perf rule); log-facade coupling (if `lib.log` backend
dispatch is too slow for per-frame stages, fall back to direct stderr write
inside diag but keep the facade for file sinks — record decision in the
module docstring).

**P0-conflicts flagged from research:** (1) coordinator sketch named the API
`dbg.*` — repo already has `debug.spl`/`debugger.spl` (interactive debugger),
so module = `diag`, functions keep the `dbg_` prefix; (2) the `[browser]`
stage helper the bug docs describe was never implemented — P0 is its first
real implementation, do not grep for existing emitters; (3) ad-hoc counters
in `ui.browser/backend.spl:305-317` stay as-is in P0 (migrating them to
`dbg_count` is optional cleanup, not required).

---

## P1 — Core session/locator/expect + TUI lane

**Goal:** prove the whole API shape on the cheapest lane (in-process TUI).

**Files to create:**
- `src/lib/nogc_sync_mut/ui_test/session.spl` (`UiTest.launch`, `UiSession`,
  `LaunchOpts`, `Lane`, teardown + `ui_test_cleanup()`),
  `locator.spl` (selector parse — split-based, no chained replace/index_of
  brace patterns; actionability poll), `expect_ui.spl` (polling matchers →
  `fail_assertion`, `spec.spl:670`), `lanes/tui.spl`.
- Extend `ui_test/types.spl` with `InjectEvent`, `UiSnapshot`, `StageEntry`
  alias to diag's, selector AST.
- Specs: `test/03_system/ui_test/core/locator_spec.spl`,
  `expect_ui_spec.spl`, `tui_lane_spec.spl` (drive
  `src/app/ui.tui/standalone.spl` or a minimal fixture app: click via
  locator, type, assert text, timeout path asserts UI-TIMEOUT bundle).

**Injection APIs to touch in existing modules:**
- `src/lib/nogc_sync_mut/play/expect.spl` — add sleep to the deadline loops
  (honor `DEFAULT_POLL_INTERVAL_MS`, `play/types.spl:44`).
- Bridge helper so `PlayError` → `fail_assertion` (in play/, small).
- TUI driver wires the existing `inject_event: fn(UIEvent)` surface
  (`ui.test_api/handler.spl:44`) and captures `Screen.render()`
  (`ui.tui/screen.spl:449`) + `tui_semantic_snapshot` (`backend.spl:131`);
  locator resolves via SGTTI (`sgtti.spl:196` `find_nodes`).

**Acceptance evidence:** `check-ui-test-core-evidence.shs` — specs pass
(grep-verified); a deliberately-missing selector times out in
< timeout+2 s, fails the test, and the dump contains stage history (P0) and
snapshot candidate count; poll loop verified sleeping (CPU time ≪ wall
time, assert via `/usr/bin/time` or rusage keys in evidence.env).
**Risks:** interpreter it-block caveat (gate greps output); SGTTI snapshot
staleness (`max_age_ms`) vs poll interval tuning; `to_be_true/false`
rejection (use `to_equal(true)`).

## P2 — GUI lane (hosted_entry injection + readback asserts)

**Goal:** drive the real GUI (`src/os/hosted/hosted_entry.spl`) as a
subprocess with dispatch-tier injection and pixel asserts.

**Files:** `ui_test/lanes/gui.spl`; `ui_test/pixels.spl` (region checksum /
golden / budgets; PPM via `encode_ppm_p6` `ppm_decode.spl:111`; diff via
`diff_buffers` `backend_parity.spl:428`; `dbg_provenance` on every
readback); specs `test/03_system/ui_test/gui/*_spec.spl` (launch → stage
`first-frame-drawn` reached; click a WM titlebar button via locator; wheel
event; region checksum of a window corner; teardown kills child).

**Injection APIs to add to existing modules (named in research):**
- `src/os/hosted/hosted_entry.spl` — `EVT_MOUSE_WHEEL` branch →
  new `HostCompositor.handle_wheel(dx, dy)` in
  `src/os/compositor/host_compositor_entry.spl` → `wm_lifecycle_wheel` in
  `wm_action_applier.spl` (fixes the dropped-wheel gap).
- `src/os/hosted/hosted_entry.spl` — `--ui-test-control` channel: drain
  control requests each loop iteration; replay `InjectEvent` through
  `comp.pointer_move` (`host_compositor_entry.spl:322`),
  `comp.handle_left_button` (`:342`), key branch (`hosted_entry.spl:133-148`);
  answer snapshot/readback/stage-log queries (readback via
  `read_pixels_with_source`, `engine2d/engine.spl:852`).
- Evidence records `inject_tier=dispatch`; the existing Linux xdotool gate
  (`check-linux-hosted-wm-live-window-evidence.shs`) remains the os-tier
  proof.

**Acceptance evidence:** `check-ui-test-gui-evidence.shs` — spec run under
`SIMPLE_EXECUTION_MODE=interpret SIMPLE_2D_BACKEND=cpu`; keys:
stage-sequence order, `wheel_delivered=1` (via `dbg_event_hop` trace),
region checksum match, `readback_source` recorded, no orphan pids.
**Risks:** JIT-winit panic (interpret-only — enforced by driver); macOS
frontmost/window quirks (duplicate bundle-id silent no-launch — memory);
control-channel transport hitting the interpreter TCP write-after-read bug
(mitigate: file/fifo-based control instead of sockets on first
implementation; the loop polls each frame anyway).

## P3 — Web lane, simple-2d core backend

**Goal:** locator/inject/assert against the pure-Simple web renderer.

**Files:** `ui_test/lanes/web_simple2d.spl`; specs
`test/03_system/ui_test/web/simple2d_*_spec.spl` (small fixture HTML;
click via widget_id locator → `UIEvent.Action` observed; typed text
round-trip; region pixel assert on 320×240 viewport).

**Injection APIs to touch:** test-session `Capability.InputInject` grant
(env/config-gated) in `src/app/ui.web/wm_bridge.spl` (`:69`) /
`ui_routes.spl:211`; driver sends the same `{t:'input_event'}` frames as
`wm.js:1216` into `WmBridge.handle_input` (`wm_bridge.spl:61`); auto-wait
"settled" reads the pipeline counters
(`ui.browser/backend.spl:305-317`, enqueued == dispatched).

**Acceptance evidence:** `check-ui-test-web-simple2d-evidence.shs` — keys:
`inject_tier=queue`, input counter deltas, region checksum, per-action
latency, and `pixel_budget_respected=1` (frame assert refused/failed fast
when over budget).
**Risks:** ~6 min/frame full-page render bug (design guards: small viewport,
region-only, budget asserts — do NOT wait for the fix); TCP
write-after-read bug on the WS control path (same fifo fallback as P2);
capability gate accidentally left open in production (default off,
spec asserts it's off without the env).

## P4 — Web lane, chrome backend (CDP)

**Goal:** CSS-selector locators + CDP input on real Chrome.

**Files:** `ui_test/lanes/web_chrome.spl`; pure-Simple CDP client (extend
`play/` — `launcher.spl:61` readiness already exists; add ws client +
`Input.dispatchMouseEvent/dispatchKeyEvent`, `Runtime.evaluate` for
locator resolution, `Page.captureScreenshot` region for pixels); fallback
shim `tools/ui-test-cdp-relay.js` (≤150 lines, stdio↔ws transport ONLY) if
the TCP bug bites; specs `test/03_system/ui_test/web/chrome_*_spec.spl`.

**Acceptance evidence:** `check-ui-test-web-chrome-evidence.shs` — click a
DOM button and observe DOM state change via polling `expect_ui`; keys:
`transport=pure_simple|relay_shim` (honesty), screenshot-region checksum
vs `tools/chrome-live-bitmap` convention.
**Risks:** interpreter TCP write-after-read bug (explicit fallback path is
part of the phase, and the evidence key records which transport ran);
headless Chrome availability on CI hosts; CDP protocol drift (pin the
handful of methods used).

## P5 — Clock / animation control

**Goal:** virtual time + frame stepping + animation asserts (design §4).

**Files:** `ui_test/clock.spl` (`FrameClock` trait, `WallClock`,
`TestClock`); `session.capture_frames(n, region?)`,
`expect_frame_stable_after`, `expect_frame_under_ms`,
`frame_stats`; specs `test/03_system/ui_test/clock/*_spec.spl`
(TUI blink/progress fixture: `run_frames(3)` → deterministic checksum
sequence; GUI: window-open animation settles by frame N; wall-clock
default proves zero behavior change).

**Injection APIs to touch:** `src/os/compositor/compositor.spl` — `clock:
FrameClock` field + `with_backends` wiring (next to `InputBackend`, `:46`),
replace direct time/sleep in the frame loop; `src/app/ui.tui/async_app.spl`
loop takes the clock; WebChrome maps to CDP `Emulation.setVirtualTimePolicy`
(P4 client).

**Acceptance evidence:** `check-ui-test-clock-evidence.shs` — same fixture
run twice under TestClock yields identical per-frame checksums
(determinism key `frames_deterministic=1`); compositor frame-time
before/after WallClock refactor within noise (perf rule).
**Risks:** hidden wall-clock reads inside app code (animations that read
`rt_time_now_*` directly bypass the clock — audit + document; fix by
routing through clock where found); or-pattern match early-return gotcha in
loop refactors (memory: mobile-gui project).

## P6 — Electron lane + evidence-gate migration demos

**Goal:** Electron driver + prove coexistence by migrating 2–3 existing
gates onto `session.write_evidence`.

**Files:** `ui_test/lanes/electron.spl` (launch via existing
`ui.electron` shell; inject via preload `sendInput` envelope →
`ipcMain.on('simple-input')`, `preload.js:4`/`bridge.js:17`; capture via
`tools/electron-live-bitmap/capture_html_argb.js` conventions, box-downsample
for Retina 2x — memory: `bug_electron_capture_2x_retina`);
`ui_test/evidence.spl` (`session.write_evidence(path, prefix)`); specs
`test/03_system/ui_test/electron/*_spec.spl`.

**Migration demos (rewrite gate internals, keep gate names + key namespaces
stable so CI consumers don't change):**
1. `check-macos-metal-browser-backing-evidence.shs` — pixel captures +
   checksums come from a UiTest spec; keys unchanged.
2. `check-linux-hosted-wm-live-window-evidence.shs` — keep xdotool os-tier
   injection, but assertions/log-marker checks go through the spec +
   `write_evidence`.
3. One `*-bitmap-evidence.shs` of the maintainer's choice (smallest).

**Acceptance evidence:** migrated gates emit byte-compatible `*_status`
keys and pass on the same hosts they pass today; new
`check-ui-test-electron-evidence.shs` proves click→IPC→Simple round trip
(`dbg_event_hop` chain visible end-to-end).
**Risks:** Electron capturePage 2x-Retina stride artifacts (known fix:
box-downsample); duplicate bundle-id silent no-launch (memory); gate
key-compat regressions (diff old/new evidence.env in the phase itself).

---

## Phase → filed-bug exposure matrix

| Filed bug / constraint | P0 | P1 | P2 | P3 | P4 | P5 | P6 |
|---|---|---|---|---|---|---|---|
| JIT panics on winit (interpret-only) | – | – | ✕ | ✕ | – | ✕ | ✕ |
| Web pixel ~6 min/frame (quadratic CSS) | probe helps find it | – | – | ✕ guard | – | ✕ budgets | – |
| Interpreter TCP write-after-read | – | – | ✕ (fifo fallback) | ✕ | ✕ (relay fallback) | – | – |
| Interpreter runner loads-only caveat | ✕ gates grep | ✕ | ✕ | ✕ | ✕ | ✕ | ✕ |
| `as u8` push marshalling (PPM) | – | – | ✕ (use lib encoder) | ✕ | – | – | ✕ |
| index_of brace / chained-replace | – | ✕ (selector parser) | – | – | – | – | – |
| Dual handle-table / seed-only policy | – | – | ✕ (why dispatch-tier) | – | – | – | – |
| Electron Retina 2x capture | – | – | – | – | – | – | ✕ |
| play/ busy-spin (fixed in P1) | – | ✕ fix | – | – | – | – | – |

## Definition of done (whole effort)

All seven gates green on the deployed pure-Simple binary; one spec per lane
in `bin/simple test` discovery; spipe-docgen manuals generated under
`doc/06_spec/`; design §8/§9 decisions revisited against implementation
reality and this plan updated with outcomes.
