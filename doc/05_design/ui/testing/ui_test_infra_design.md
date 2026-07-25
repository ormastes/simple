# UI Test Infrastructure — Design (Playwright-like API for Simple)

**Date:** 2026-07-05
**Research basis:** `doc/01_research/ui/testing/ui_test_infra_research.md`
(all file:line claims verified there).
**Plan:** `doc/03_plan/ui/testing/ui_test_infra_plan.md`.

## Status / honesty

- **Exists today (reused, not redesigned):** std.spec BDD core;
  `std.play` polling expect/locator/timeouts/CDP launcher; SGTTI snapshot
  driver; `ui.test_api` `inject_event` surface; `WmBridge.handle_input`;
  `InputBackend` trait; `Engine2DReadback` honest readback; golden gate +
  evidence.env conventions; TUI `Screen.render()` string capture; engine3d
  CPU rasterizer.
- **Designed here (new):** `UiTest` session facade; per-lane drivers behind a
  `UiLane` trait; unified locator with per-lane selector resolution;
  actionability auto-wait; std.spec bridging of polling asserts; budget-aware
  pixel asserts; `TestClock` virtual clock + frame-loop seam; a shared
  **debug/diagnostics primitive set `std.diag`** (§8 — stage tracer,
  cooperative watchdog, aggregating timers/counters, event-chain tracer,
  provenance assert) that the test infra consumes for its hang/slow
  detection; per-action/per-frame budget asserts; teardown protocol.
- **Deferred:** hardware-3D lane (engine3d GPU backends are stubs);
  macOS OS-level CGEvent injection; winit-queue synthetic injection
  (`rt_winit_inject_event` — seed change, bootstrap-only policy + dual
  handle-table hazard); Playwright-style full trace recording;
  browser contexts/isolation; codegen/recorder.

---

## 1. Core model

### 1.1 One facade, five lanes, one trait

```simple
use std.ui_test

val session = UiTest.launch(Lane.Tui, "src/app/editor/tui_main.spl", LaunchOpts.default())
session.locator("button#save").click()
expect_ui(session.locator("statusbar")).to_have_text("saved")
session.close()
```

- `Lane` enum: `Tui | Gui | WebSimple2d | WebChrome | Electron | Scene2d | Scene3d`.
  (`Scene2d`/`Scene3d` are the engine2d/engine3d in-process lanes.)
- `UiSession` is a **struct composed with a `UiLane` trait object** — NO
  inheritance, per repo rule. Each lane driver implements:

```simple
trait UiLane:
    fn launch(app: text, opts: LaunchOpts) -> Result<LaneHandle, UiTestError>
    fn snapshot(handle) -> UiSnapshot           # widget/DOM/region tree, ≤ max_age_ms fresh
    fn inject(handle, ev: InjectEvent) -> Result<(), UiTestError>
    fn read_pixels_region(handle, x, y, w, h) -> Result<PixelRegion, UiTestError>
    fn stage_log(handle) -> [StageEntry]        # for timeout dumps
    fn clock(handle) -> ClockHandle?            # nil if lane has no virtual clock yet
    fn close(handle) -> Result<(), UiTestError>
```

- `LaunchOpts`: viewport `(w, h)` (default **small**: 320×240 for pixel-budget
  reasons, §5), `backend` (`SIMPLE_2D_BACKEND` value), `mode`
  (`in_process | subprocess`), `env: [(text, text)]`, `timeout_ms`
  (default `DEFAULT_LAUNCH_TIMEOUT_MS = 30000`, reused from
  `play/types.spl:43`), `require_device_readback: bool` (default false).
- Launch modes: TUI/Scene2d/Scene3d run **in-process** (create the
  Screen/Engine directly); GUI/Web/Electron run as **subprocess** via
  `bin/simple run … ` with `SIMPLE_EXECUTION_MODE=interpret` (JIT-winit filed
  bug) and a control channel (§4 per lane).

### 1.2 Locator model (lazy queries, Playwright-style)

`session.locator(selector)` returns a `Locator` — a **query description**, not
an element handle. It is re-resolved against a fresh `UiSnapshot` at *every*
action and assertion (never stale). Selector grammar, kept deliberately tiny
(a full CSS engine is out of scope):

```
selector  := kind? ('#' id)? (':' pseudo)* ('=' text-eq)?
kind      := 'button' | 'input' | 'text' | 'list' | 'window' | 'region' | <role>
text-eq   := "text=Save"  (exact) | "text*=Sav" (contains)
```

Per-lane resolution:

| Lane | Snapshot source | `button#save` resolves via |
|---|---|---|
| Tui / Gui | SGTTI accessibility snapshot (`ui_test/sgtti.spl:178`, `find_nodes:196`) over `UIState` / Draw IR | node role + widget id |
| WebSimple2d | pure-Simple DOM/layout tree (widget_id path used by `wm.js:1216` / `wm_bridge.spl:61`) | element id / role in layout tree |
| WebChrome / Electron | CSS selector passed through verbatim to CDP (`document.querySelector` semantics) | native CSS |
| Scene2d / Scene3d | **named-region registry** (new, §4.5): tests or apps register `region("save", x, y, w, h)`; 3D adds scene-node names (`scene_graph3d.spl:7`) | registry lookup |

Locator API: `click()`, `dblclick()`, `type(text)`, `key(name, mods)`,
`wheel(dx, dy)`, `drag_to(other | (x,y))`, `hover()`, `bounds() -> Rect?`,
`count()`, `nth(i)`. Selector parsing must avoid the chained-`replace` /
`index_of`-brace-needle bugs — implement with `split`-based scanning
(memory: `bug_index_of_brace_needle`).

### 1.3 Auto-wait / actionability (the hang detector)

Every action performs, before injecting:

1. **resolve** — locator finds exactly one node (else keep polling).
2. **visible** — node visible flag in snapshot (`check_visible` semantics,
   `sgtti.spl:208`).
3. **stable** — `bounds()` identical across two consecutive snapshots ≥ one
   frame apart (animation settled).
4. **enabled** — `check_enabled` semantics (`sgtti.spl:216`).

Poll loop: deadline = `DEFAULT_ACTION_TIMEOUT_MS` (30 000, `play/types.spl:41`)
unless overridden per action; poll interval = `DEFAULT_POLL_INTERVAL_MS` (100,
`play/types.spl:44`) **with a real sleep** — this fixes the existing
busy-spin defect in `play/expect.spl` rather than adding a second loop.
The deadline is armed via the std.diag cooperative watchdog
(`dbg_deadline`, §8.2), so the breach path and its stage-history dump are
identical whether a hang is caught by a test or by an instrumented app during
production debugging.

**On timeout → the action FAILS the test** and emits a diagnostic bundle:

```
UI-TIMEOUT action=click selector=button#save lane=gui waited_ms=30000
stage-log: args-parsed=+0ms backend-selected=+41ms … last=render-frame-start (+1207ms, 28793ms ago)
snapshot: 14 nodes, candidates for 'button#save': 0
last-frame: checksum=482910233 source=cpu_mirror
```

The stage-log dump is what turns a timeout into a *diagnosis*: the last stage
reached tells you where it hung (per the stage sequence in
`doc/08_tracking/bug/browser_engine_css_size_quadratic_pixel_render_2026-07-04.md:214-222`
— which this design finally implements, §6). Failure is reported through
std.spec `fail_assertion` (`spec.spl:670`) so it appears in `print_summary`.

### 1.4 Polling assertions bridged into std.spec

New module `expect_ui(locator)` / `expect_session(session)` wraps the
existing `play/expect.spl` machinery and **bridges results into std.spec**:

```simple
expect_ui(session.locator("statusbar")).to_have_text("saved")      # polls to deadline
expect_ui(session.locator("dialog")).to_be_visible()
expect_ui(session.locator("dialog")).not_().to_be_visible()
expect_session(session).to_have_window_count(2)
```

- Matchers: `to_have_text`, `to_contain_text`, `to_be_visible`, `to_be_hidden`,
  `to_be_enabled`, `to_be_focused`, `to_have_count`, `to_have_value`,
  `to_have_bounds(rect, tolerance)`.
- Implementation reuses `LocatorExpect` (`play/expect.spl:54`) poll-to-deadline
  pattern (+sleep fix); on failure calls `fail_assertion(message)` — closing
  the existing gap where `PlayError` results never reach `print_summary`.
- Do **not** use `to_be_true/to_be_false` internally (runner rejects them);
  use `to_equal(true)`/`assert_true` per `.claude/rules/testing.md`.

### 1.5 Pixel assertions — budget-aware by design

Full-page web pixel render is ~6 min/frame today (quadratic-CSS filed bug);
the design assumes that is NOT fixed. Three cost tiers, cheapest first:

```simple
# Tier 1 — checksum of a region (u32 pixel sum, repo convention)
session.expect_region_checksum(x, y, w, h, 482910233)

# Tier 2 — golden compare of a region (PPM P6, exact, REGEN_GOLDENS to refresh)
session.expect_region_golden(x, y, w, h, "test/03_system/gui/ui_test/goldens/save_button.ppm")

# Tier 3 — full-frame golden (only for small viewports; refuses > budget)
session.expect_frame_golden("…/frame.ppm")
```

- All readbacks go through `read_pixels_with_source()`
  (`engine2d/engine.spl:852`) and record `readback_source` in the failure
  message and evidence, with a `dbg_provenance` check (§8.2) on every
  readback. If `LaunchOpts.require_device_readback` is set and
  source ≠ `device_readback`, the assert fails (honest-GPU mode for evidence
  gates); default mode accepts `cpu_mirror` (deterministic CI on
  `SIMPLE_2D_BACKEND=cpu`).
- **Budget guard:** each pixel assert takes `budget_ms` (default 10 000). The
  driver estimates cost (viewport area × lane cost factor); if estimated or
  actual time exceeds budget, the assert fails with `PIXEL-BUDGET-EXCEEDED`
  rather than hanging the suite. For the WebSimple2d lane while the CSS bug
  is open: default viewport 320×240, region asserts only,
  `expect_frame_golden` requires explicit `budget_ms` override.
- Golden handling reuses `wm_compare/golden_gate.spl` conventions:
  `goldens_dir` layout, `REGEN_GOLDENS` env (`:150`), exact `pass_exact`
  compare via `diff_buffers` (`backend_parity.spl:428`). PPM writing uses
  `encode_ppm_p6` (`src/lib/common/image/ppm_decode.spl:111`) — never a new
  encoder (u8-cast marshalling bug is documented there).

### 1.6 Slow detection

```simple
session.expect_action_under_ms(200): session.locator("button#tab2").click()
session.expect_frame_under_ms(33)                   # last presented frame
val stats = session.frame_stats(last_n: 60)          # {p50, p95, max, count}
```

Frame timing comes from the same instrumentation as the stage log (§6) plus
the std.diag aggregating timers (§8.2) — the frame loop stamps
`render-frame-start`/`frame-presented` entries and `dbg_time_begin/end`
around render/layout/paint; the WebSimple2d lane can additionally read the
existing pipeline counters (`ui.browser/backend.spl:305-317`).

---

## 2. Event injection layering (per-lane injection points)

**Principle:** inject at the *same queue real OS input enters* when such a
queue exists; where it does not, inject at the first dispatch seam below it
and **label the tier in evidence** (`inject_tier=queue|dispatch|os`).

| Lane | Tier used | Injection point (from research) | Notes |
|---|---|---|---|
| Tui | queue | `inject_event: fn(UIEvent)` callback (`ui.test_api/handler.spl:44`) feeding the app's event loop — same channel `poll_event` (`ui.tui/backend.spl:90`) consumes | already exists; wire drag/wheel variants |
| Gui (hosted WM) | dispatch (default) | `comp.pointer_move` (`host_compositor_entry.spl:322`), `comp.handle_left_button` (`:342`), key branch (`hosted_entry.spl:133-148`) — the *exact* calls the winit poll loop makes | there is no Simple-side queue; this IS the first seam below winit |
| Gui (hosted WM) | os (evidence gates, Linux) | `xdotool` per `check-linux-hosted-wm-live-window-evidence.shs:120-131` | real end-to-end; kept for gate-tier proofs |
| Gui — winit queue | **deferred** | `rt_winit_inject_event` into `EVENTS` (`winit_sffi/mod.rs:43`) | seed change (bootstrap-only policy) + dual-handle-table hazard; revisit when a seed release is scheduled anyway |
| WebSimple2d | queue | `WmBridge.handle_input` (`wm_bridge.spl:61`) with a `Capability.InputInject`-granted test session (`:69`) — same entry real WS clients use | the control channel sends the same `{t:'input_event'}` frames as `wm.js:1216` |
| WebChrome | queue (browser-native) | CDP `Input.dispatchMouseEvent`/`dispatchKeyEvent` over the DevTools WebSocket (launcher readiness via `play/launcher.spl:61`) | see §3 JS-shim boundary |
| Electron | queue | preload `sendInput` envelope → `ipcMain.on('simple-input')` (`preload.js:4`, `bridge.js:17`) | shim already exists; test control channel triggers `window.simpleUI.sendFrame` |
| Scene2d | queue | scripted fake `InputBackend` (`input_backend.spl:4-10`) passed via `Compositor.with_backends` (`compositor.spl:46`), drained by `_handle_input_backend` (`:347`) — identical consumption path to real winit input | cleanest seam in the repo |
| Scene3d | n/a | no interactive 3D app exists; injection deferred with the lane | capture-only sessions still work |

**New injection APIs required in existing modules** (all pure Simple):

1. `hosted_entry.spl` — add `EVT_MOUSE_WHEEL` branch →
   `comp.handle_wheel(dx, dy)` (new method on HostCompositor →
   `wm_lifecycle_wheel`). Fixes the dropped-wheel gap for real users AND
   tests.
2. `hosted_entry.spl` — optional `--ui-test-control=<port|fifo>` flag: when
   set, each loop iteration drains a control channel and replays
   `InjectEvent`s through the same dispatch calls as the winit branch, and
   answers snapshot/readback/stage-log requests. (This is the GUI lane's
   `LaneHandle`.) Reuses the `ui.test_api` handler surface rather than a new
   protocol.
3. `wm_bridge.spl` — a test-session capability grant path so
   `Capability.InputInject` is satisfiable headlessly (config/env-gated,
   default off in production).
4. `Compositor` — accept `clock: FrameClock?` (§4) alongside `InputBackend`.

`InjectEvent` is one shared enum (`PointerMove/PointerDown/PointerUp/Wheel/
Key/Char/Drag`) that each driver translates to its native form (UIEvent,
compositor call, CDP payload, IPC envelope, KeyEvent/MouseEvent). Every
injected event carries a chain id stamped into the std.diag event-chain
tracer (§8.2) so a vanished click is traceable hop-by-hop.

---

## 3. Architecture & placement

### 3.1 Modules

```
src/lib/nogc_sync_mut/diag.spl            # P0 — std.diag debug primitives (§8); other variants re-export
src/lib/nogc_sync_mut/ui_test/            # grows (already: client, http, parse, sgtti, types)
  session.spl        # UiTest.launch, UiSession, LaunchOpts, teardown protocol
  locator.spl        # selector parse + resolve loop + actionability
  expect_ui.spl      # polling matchers bridged to std.spec fail_assertion
  pixels.spl         # region readback, checksum, golden compare, budgets
  clock.spl          # FrameClock trait + TestClock (§4)
  stage_log.spl      # thin adapter over std.diag stage tracer (§6, §8 — P0 owns the primitive)
  lanes/             # one driver per lane (UiLane impls)
    tui.spl  gui.spl  web_simple2d.spl  web_chrome.spl  electron.spl  scene.spl
```

**Justification (stdlib variant matrix):** `nogc_sync_mut` is where `spec/`,
`play/`, `test_runner/`, and the existing `ui_test/` already live — sync,
mutable, FFI-capable, no GC dependency; test infra must run under the
deployed self-hosted binary in interpret mode. Cross-lane pure types
(`InjectEvent`, `UiSnapshot`, selector AST) go in the existing
`ui_test/types.spl`. Nothing goes in `src/app/` except thin app-side hooks
(control-channel flag in `hosted_entry.spl`, test mount in `ui.browser`),
because the library must be importable by any spec as `use std.ui_test`.

**Relationship to std.play:** play/ remains the low-level browser/CDP toolkit;
`ui_test/` composes it (timeout constants, expect polling, launcher). The
poll-sleep fix and the std.spec bridge are patches **in play/**, benefiting
both layers. No `X2` module split (repo rule): we extend `ui_test/`, we do
not create `ui_test2/` or fork play/.

### 3.2 MDSOC+ decomposition

Userland service → MDSOC outer + ECS-flavored core state per
`doc/04_architecture/compiler/mdsoc_architecture_tobe.md`:

- **Dimensions:** `session` (lifecycle), `input` (injection), `query`
  (snapshot/locate), `capture` (pixels), `time` (clock), `report`
  (stage-log/evidence). Each is a module facet with its own narrow interface;
  lane drivers implement the facets they support (trait-object composition,
  no inheritance).
- **ECS-ish core:** `UiSession` is an entity id; facets store their state in
  per-facet stores keyed by session id (multiple concurrent sessions, e.g.
  Electron + WebSimple2d parity tests, stay isolated).
- Kernel/driver code (compositor, engine2d) receives only **seams** (clock
  param, InputBackend, wheel branch) — MDSOC-only, no ECS there.

### 3.3 Plugging into std.spec / bin/simple test

UI tests are ordinary `*_spec.spl` files discovered by
`is_test_file` (`test_runner_files.spl:66`) — no runner changes:

```simple
use std.spec
use std.ui_test

describe "editor save button":
    it "saves on click":            # @capture
        val s = UiTest.launch(Lane.Tui, "src/app/editor/tui_main.spl", LaunchOpts.default())
        s.locator("button#save").click()
        expect_ui(s.locator("statusbar")).to_have_text("saved")
        s.close()
```

- Follows `.claude/templates/spipe_template.spl` (step helpers, `@cover`,
  `@capture`) so spipe-docgen manuals generate as usual
  (`test_runner_main.spl:80`).
- Placement: `test/03_system/ui_test/<lane>/*_spec.spl` with
  `# @cover src/lib/nogc_sync_mut/ui_test/... 80%`.
- **Evidence caveat:** interpreter-mode runner verifies loading, not it-block
  execution — so each lane also ships one evidence gate
  (`scripts/check/check-ui-test-<lane>-evidence.shs`) that runs the specs and
  greps for `✗`/summary lines plus lane-specific `evidence.env` keys
  (`ui_test_<lane>_status=pass`, `inject_tier=…`, `readback_source=…`),
  following the existing 63-gate conventions.

### 3.4 JS shim boundaries (hard constraint: JS = thin interface only)

| Shim | File(s) | Scope allowed |
|---|---|---|
| Electron preload/bridge | existing `src/app/ui.electron/preload.js`, `bridge.js` | envelope forwarding only; no test logic |
| Chrome CDP | none preferred: pure-Simple CDP client over WebSocket (JSON, `Input.*`, `Page.*`, `Runtime.evaluate`) reusing `play/launcher.spl` | **risk:** interpreter TCP write-after-read bug (filed) may block a tight WS loop. Fallback shim: ≤150-line `tools/ui-test-cdp-relay.js` that relays newline-delimited JSON stdio ↔ CDP WebSocket — transport only, zero assertion/wait logic (all waiting stays in Simple) |
| Bitmap capture | existing `tools/chrome-live-bitmap/capture_html_argb.js`, `tools/electron-live-bitmap/…` | unchanged, already artifact-shaped |

### 3.5 Evidence-gate coexistence & migration

Existing gates keep working untouched. New helper
`session.write_evidence(path, prefix)` emits the standard flat
`key=value` env (checksums as u32 pixel sums, `*_status`, `readback_source`,
`inject_tier`, stage timings) so a gate `.shs` shrinks to: run spec →
source env → final `[ "$prefix_status" = pass ]`. Migration is opt-in,
demonstrated on 2–3 gates in plan P6; the 63-gate fleet migrates only as
gates are next touched.

---

## 4. Animation & clock control

### 4.1 FrameClock seam

New trait + two impls in `ui_test/clock.spl` (usable by non-test code too):

```simple
trait FrameClock:
    fn now_ms() -> i64
    fn sleep_until_next_frame(target_fps: i32)

class WallClock ...    # rt_time_now_unix_micros + real sleep (today's behavior)
class TestClock ...    # virtual: now advances ONLY via tick/run_frames; sleep_until = yield-to-driver
```

**Frame-loop seams (per lane):**

- **Compositor/GUI:** `Compositor` gains `clock: FrameClock` (default
  `WallClock` — zero behavior change), set via `with_backends(...)` next to
  `InputBackend` (`compositor.spl:46`). The frame loop replaces direct
  time/sleep calls with `clock.now_ms()` / `clock.sleep_until_next_frame()`.
  With `TestClock`, `sleep_until_next_frame` returns control to the test
  driver instead of sleeping — the loop runs exactly one frame per
  `run_frames(1)`.
- **Scene2d/Scene3d (in-process):** the test owns the loop; `run_frames(n)`
  literally calls render+present n times with `clock` advanced
  `1000/fps` ms per frame. Engine2D/3D need no changes (they don't read time;
  animations are app-side).
- **TUI:** `async_app.spl` loop takes the same `FrameClock`.
- **WebChrome:** map to CDP `Emulation.setVirtualTimePolicy` (advance) — the
  browser's own virtual clock; document that JS `Date.now` freezing follows
  CDP semantics, not ours.
- **WebSimple2d:** server render loop takes `FrameClock` like the compositor.

### 4.2 Test API

```simple
val clk = session.clock()!            # nil → lane has no virtual clock (assert or skip)
clk.tick(250)                          # advance virtual time, run due timers, render pending frame(s)
clk.run_frames(10)                     # step exactly 10 frames at session fps (default 60)
val frames = session.capture_frames(10)        # run 10 frames, checksum each
expect(frames.checksums).to_equal([c0, c1, c1, c2, …])       # animation keyframe assert
expect(frames.all_distinct()).to_equal(true)                  # "it animates"
session.expect_frame_stable_after(frames, 6)                  # settles by frame 6
```

`capture_frames(n, region?)` uses the region readback (budget rules of §1.5
apply per frame — default small regions for web lane). Per-frame wall-time is
recorded even under TestClock, so `expect_frame_under_ms` measures *compute*
cost per frame while virtual time stays deterministic.

---

## 5. Teardown protocol

`session.close()`: flush stage log + `dbg_summary_dump()` (§8.2) → optional
final-frame artifact on failure
(`UI_TEST_ARTIFACT_DIR`, default under `build/ui_test/<spec>/`) → lane
teardown (in-process: drop; subprocess: control-channel `quit`, then
SIGTERM after 2 s, SIGKILL after 5 s) → assert no orphan process.
`after_each` helper `ui_test_cleanup()` closes leaked sessions so a failing
`it` cannot wedge the suite (registered sessions tracked per test in the
session store).

---

## 6. Stage log (implements the design-only probe)

The stage tracer is a **std.diag primitive** (`dbg_stage`, §8.2) delivered in
plan phase P0 — the test infra consumes it, it does not own it.
`dbg_stage(component, stage)` appends `(component, stage, t_ms)` to a bounded
ring buffer AND prints `[<component>] stage <stage> +<dt>ms` to stderr —
exactly the format the bug docs specified
(`browser_engine_css_size_quadratic_pixel_render_2026-07-04.md:214-222`).
First instrumented sites: `ui.browser/app.spl` + `backend.spl` (the
originally designed sites, currently only a stale comment at
`ui.browser/main.spl:76-77`), `hosted_entry.spl` (args-parsed,
window-created, first-frame-drawn), compositor frame loop
(render-frame-start / frame-presented).

`ui_test/stage_log.spl` is a thin adapter: in-process lanes read the diag
ring buffer directly; subprocess lanes parse the stderr stage lines (stderr
is the cross-process transport — the ring buffer is per-process). Drivers
expose it via `UiLane.stage_log()`; every TIMEOUT dump includes it (§1.3);
`expect_stage_reached("first-frame-drawn", within_ms)` is the launch-hang
assert. Unlike the always-on-unless-`--quiet` bug-doc sketch, emission
follows the §8 env gating, and `UiTest.launch` sets `SIMPLE_DIAG` for its
child processes so tests always capture stages without polluting production
runs.

---

## 7. 3D seam

Same session/capture API over a scene handle — implemented now for CPU
engine3d, interaction deferred:

```simple
val s = UiTest.launch(Lane.Scene3d, "", LaunchOpts.with_size(256, 192))
val e3 = s.scene3d()!                 # the Engine3D (engine3d/engine.spl:61)
e3.set_camera(view, proj); e3.draw_cube(...)
s.clock()!.run_frames(1)
s.expect_region_checksum(0, 0, 256, 192, expected)
```

Locators resolve against scene-node names (`SceneNode3D`,
`scene_graph3d.spl:7`) for existence/transform asserts
(`expect_ui(s.locator("node#cube1")).to_be_visible()` = present +
inside frustum — frustum math exists in the CPU backend). Pointer→3D
picking, and any GPU-3D backend, are **deferred** (all non-CPU engine3d
backends are software-fallback stubs today). The `UiLane` trait needs no
change when hardware 3D lands — only the driver's `read_pixels_region`
gains a device path.

---

## 8. Debug infrastructure — std.diag (shared foundation, plan phase P0)

> **Status (2026-07-05): P0 is IMPLEMENTED** at
> `src/lib/nogc_sync_mut/diag.spl` (commit `70a5af4b`), 13/13 specs green in
> `test/01_unit/lib/nogc_sync_mut/diag_spec.spl`. P1-P6 (the session/locator/
> lane drivers below) remain design-only.

**Why here:** five recurring problem classes from this repo's actual history
are undiagnosable by default: (1) silent hangs (first-frame render hang
> 5 min with no output until stage logs were hand-added); (2) quadratic/slow
paths found only by wall-clock pain (336 KB-CSS quadratic, ~6 min/frame — no
per-stage timing or counters); (3) silent fallbacks/fakery (`read_pixels`
silently falls back to software; binaries exit 1 silently under wrong env;
GPU claimed but CPU rendered); (4) event-delivery mysteries (clicks vanish
between backend → transform → hit-test → handler with no visibility);
(5) cross-lane pixel diffs debuggable only by manual artifact comparison.
The test infra's auto-wait timeout dumps, hang detector, and slow asserts
(§1.3, §1.6) are **consumers** of these primitives, not owners. References
to `std.diag` elsewhere in this doc (§1.3 watchdog, §1.5 provenance, §1.6
timers, §2 chain ids, §5 summary dump, §6 stage tracer) all resolve to this
section's contract.

### 8.1 Extension policy — what exists, what is net-new

Per the no-duplicate-modules rule, std.diag composes existing facilities
(inventory in research §3.6, verified 2026-07-05):

| Facility | Status | Decision |
|---|---|---|
| Env-gated logging facade | EXISTS — `src/lib/nogc_sync_mut/log.spl` (reads `SIMPLE_LOG` once at load, ~no-op when off; `_emit:113` → stderr + `lib.log` backends; other mut variants re-export it) + `src/lib/log.spl` backend registry (`log_register_backend:257`, `RingBackend:292`) | diag emits **through** this facade; adopts its load-once gating pattern |
| Deadline guard | EXISTS — `src/lib/nogc_sync_mut/failsafe/timeout.spl` (`Deadline` `:109`, `check()` `:118`, `TimeoutManager:53`) | watchdog composes `Deadline`; no new deadline type |
| Perf stats aggregation | EXISTS — `src/lib/nogc_sync_mut/perf.spl` (`ComponentStats`/`PerfStats:143-217`) — benchmark-oriented, heavyweight | diag keeps its own flat label→(count,total,max) map, exports into `PerfStats` shape on demand |
| Call-tracing | EXISTS — `aop_debug_log.spl` (`SIMPLE_AOP_DEBUG`-gated enter/exit ring) | untouched; diag is site-targeted, not function-wrapping |
| Interactive debugger | EXISTS — `nogc_sync_mut/debug.spl`/`debugger.spl` | **name collision hazard**: the new module is `diag`, NOT `dbg`/`debug`, to avoid colliding with these |
| Stage tracer `[comp] stage NAME` | MISSING (only stale comment `ui.browser/main.spl:77`) | net-new in diag |
| Watchdog | MISSING (no watchdog module repo-wide) | net-new in diag (cooperative) |
| General counters registry | MISSING (`ui.browser/backend.spl:306-317` counters are ad-hoc struct fields) | net-new in diag |

### 8.2 Contract (module path, API, env vars)

**Module:** `src/lib/nogc_sync_mut/diag.spl` (single file; other mut variants
re-export, following the `log.spl` shim chain). Import: `use std.diag`.
All functions are `dbg_`-prefixed free functions (module-level, matching the
`log_info(...)` convention; state is module-level like `log.spl`).

```simple
# Stage tracer — generalizes the ad-hoc [browser] stage logs
dbg_stage(component: text, stage: text)
    # gated-off: single bool check. on: ring-append (cap 256) +
    # "[<component>] stage <stage> +<delta_ms>ms" via log facade (stderr)
dbg_stage_history() -> [StageEntry]          # StageEntry{component, stage, t_ms}
dbg_stage_dump()                             # loud stderr dump of the ring

# Cooperative watchdog — no threads; interpreter-safe (P0)
dbg_deadline(label: text, budget_ms: i64)    # arms; composes failsafe Deadline
dbg_deadline_check(label: text) -> bool      # also auto-checked inside dbg_stage
    # breach → ONE loud stderr block: label, budget, elapsed, stage history dump
dbg_deadline_clear(label: text)

# Aggregating timers/counters — the quadratic-path finder
dbg_time_begin(label: text)
dbg_time_end(label: text)                    # accumulates count/total_ms/max_ms
dbg_count(label: text, delta: i64)
dbg_summary() -> text                        # "label count=N total=Tms max=Mms" per label
dbg_summary_dump()                           # at exit by instrumented apps / session.close()

# Event-chain tracer — one line per hop
dbg_event_hop(chain_id: text, hop: text, detail: text)
    # "[event <chain_id>] <hop> <detail>", e.g.
    # "[event c42] hit_test x=12 y=40 verdict=miss top_widget=none"
dbg_events_on() -> bool                      # guard for expensive detail construction

# Provenance assert — anti-fakery
dbg_provenance(claimed: text, actual: text, context: text)
    # actual != claimed → ALWAYS-ON loud warning (not env-gated) + counter
    # "DIAG-PROVENANCE context=readback claimed=device_readback actual=cpu_mirror"
```

**Env gating:** master var `SIMPLE_DIAG` (read **once at module load**, zero
work when unset — the `log.spl` pattern): `SIMPLE_DIAG=all` or a comma list
of facets `stage,watchdog,timers,events`. Follows the existing
`SIMPLE_<SUBSYS>_DEBUG` convention. `dbg_provenance` warnings are always on
(a silent-fakery detector that is itself silenceable would be pointless);
only its per-hit verbosity is facet-gated. `SIMPLE_DIAG_FILE` optional file
sink (delegates to the log facade's file support).

**Cost rule:** every `dbg_*` call compiles to one module-level bool test when
`SIMPLE_DIAG` is unset — no string formatting, no time syscalls. Callers must
not pre-format `detail` strings outside a facet check in hot loops; use
`dbg_events_on()` etc. to guard expensive detail construction.

### 8.3 Mapping to the five problem classes

| Problem class | Primitive + first instrumentation sites |
|---|---|
| Silent hangs | `dbg_stage` at the §6 sites (`ui.browser`, `hosted_entry`, compositor frame loop) + `dbg_deadline("first-frame", 15000)` armed at launch; breach dumps stage history — "hung at render-frame-start" instead of silence. UiTest timeouts (§1.3) reuse the same dump. |
| Quadratic/slow paths | `dbg_time_begin/end` around css-apply / layout / paint / per-widget draw; `dbg_summary_dump()` at exit prints count/total/max per label — a 336 KB-CSS quadratic shows up as `css_apply count=180000 total=350000ms` instead of a 6-minute mystery. `session.frame_stats` (§1.6) reads the same aggregates. |
| Silent fallbacks | `dbg_provenance` at every readback consumer (`pixels.spl`, presenters like `simple_web_html_engine2d_presenter.spl:19-30`), backend resolve (`requested_backend` vs `resolved_backend`), and execution-mode guards (JIT-vs-interpret expectations). `require_device_readback` (§1.5) escalates the same check from warning to failure. |
| Event-delivery mysteries | `dbg_event_hop` with one chain id per injected/OS event at: ingest (`WmBridge.handle_input` `wm_bridge.spl:61` / winit branch `hosted_entry.spl:107-160` / fake `InputBackend` drain `compositor.spl:347`), coordinate transform, hit-test verdict (`wm_action_applier.spl`), dispatch (`session.dispatch`), handler entry. A vanished click's trace ends at the exact hop that dropped it. UiTest `inject()` stamps the chain id so test logs correlate. |
| Cross-lane pixel diffs | diag supplies the timers/provenance side; the pixel side is §1.5's region/golden asserts plus a `dbg_count("pixel_diff.first_mismatch_at", idx)`-style breadcrumb emitted by `diff_buffers` consumers. Full visual-diff tooling stays in the existing parity/evidence machinery. |

### 8.4 Parallel-implementation note

P0 is being implemented by a separate agent from this same primitive list.
The contract this design (and the P1+ phases) depends on is exactly §8.2:
module `src/lib/nogc_sync_mut/diag.spl`, the `dbg_*` names above,
`SIMPLE_DIAG` facet gating, stderr line formats
`[<component>] stage <stage> +<delta>ms` and `[event <id>] <hop> <detail>`
(UiTest subprocess drivers parse these — format changes break the GUI-lane
stage fetch), ring cap 256, cooperative (thread-free) watchdog. Known
conflicts flagged: (a) do NOT name the module `dbg`/`debug` — collides with
the existing interactive debugger modules; (b) emit through
`nogc_sync_mut/log.spl`'s facade rather than raw `print` so ring/file
backends keep working; (c) compose `failsafe/timeout.spl` `Deadline` rather
than defining a second deadline type.

---

## 9. Design decisions wanting review

1. **Extend std.play + ui_test/ in place** (fix busy-spin & spec-bridge in
   play/) instead of a fresh framework — maximal reuse, but couples the new
   API to play/'s current shape.
2. **GUI lane injects at compositor dispatch (Tier "dispatch"), not the winit
   queue** — queue injection needs a seed extern (bootstrap-only policy +
   dual-handle-table risk). Evidence records `inject_tier` so gates can
   still demand `os`-tier via xdotool on Linux.
3. **Pure-Simple CDP client first, stdio relay shim as fallback** — bets
   against the interpreter TCP write-after-read bug biting the DevTools
   WebSocket loop; the fallback keeps all logic in Simple but adds a JS
   transport process.
4. Exact-match pixel asserts only (repo convention `pass_exact`) — no
   tolerance/perceptual gate in v1; small-region goldens keep flake low.
5. `FrameClock` default-`WallClock` threading through compositor/TUI loops —
   small diffs in hot loops; must be perf-neutral (verify frame-time before/
   after, per repo perf rule).
6. **std.diag as one new module composing log/failsafe/perf** (not a facet
   of any of them), named `diag` (not the sketched `dbg.*`) to dodge the
   existing `debug.spl`/`debugger.spl` collision, with `dbg_provenance`
   always-on rather than env-gated.
