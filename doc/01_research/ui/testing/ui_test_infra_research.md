# UI Test Infrastructure — Research Survey

**Date:** 2026-07-05
**Scope:** Survey of everything the repo already has for a Playwright-like UI test
infrastructure covering four lanes — TUI, GUI (hosted WM), Web (chrome backend +
simple-2d core backend), 2D/3D (engine2d/engine3d) — with event injection,
animation/clock control, state + pixel assertions, and hang/slow detection.
**Companion docs:** design `doc/05_design/ui/testing/ui_test_infra_design.md`,
plan `doc/03_plan/ui/testing/ui_test_infra_plan.md`.

## Status / honesty

- Everything in this document **exists today** unless explicitly marked
  **MISSING** or **DESIGN-ONLY**. All file:line references were verified against
  the working tree on 2026-07-05.
- Two prior assumptions were overturned by this survey:
  1. The repo is **not** starting from zero on a Playwright-like API — a
     `std.play` module (`src/lib/nogc_sync_mut/play/`) already implements
     polling `expect`, locators, wait helpers, and a CDP launcher.
  2. The repo is **not 2D-only** — a working CPU-rasterizer 3D engine
     (`engine3d`) exists with camera, scene graph, depth buffer, and
     `read_pixels()`. Only hardware-accelerated 3D is missing.
- One prior assumption was **falsified**: the `[browser]` stage logs
  (args-parsed → first-frame-drawn) are **DESIGN-ONLY** — documented in bug
  docs, zero hits in source (see §3.4).

---

## 1. Existing spec framework (std.spec)

Core lives in `src/lib/nogc_sync_mut/spec.spl`; the `spec/` subdirectory holds
skip/ignore conditions, env detection, and feature-doc metadata. The same tree
is mirrored per memory lane (`gc_sync_mut`, `gc_async_mut`, `nogc_async_mut`,
`common`).

### 1.1 Structure and lifecycle

| Facility | Location |
|---|---|
| `describe(name, block)` | `src/lib/nogc_sync_mut/spec.spl:61` |
| `context(name, block)` | `spec.spl:72` |
| `it(name, block)` → `_execute_it` | `spec.spl:112` → `:82` |
| aliases `test`/`example`/`specify` | `spec.spl:117/120/123` |
| `slow_it` (runs under `SIMPLE_TEST_FILTER=slow`) | `spec.spl:131` |
| `step(description)` — docgen marker, no-op at runtime | `spec.spl:126` |
| `before_each` / `after_each` | `spec.spl:485` / `:488` |
| `before_context` (immediate, once) | `spec.spl:216` |
| `skip_it` / `pending` / `skip` | `spec.spl:170/180/187` |
| platform skips (`skip_on_windows` etc.) | `spec.spl:279-421` |
| summary + exit code | `print_summary` `spec.spl:726`, `get_exit_code` `:746` |

**Gap:** no suite-level `before_all`/`after_all` (only per-example hooks +
immediate `before_context`). The `__init__.spl` docstring advertises
`before`/`after` but they are not defined.

### 1.2 Matchers

Entry: `expect(value)` `spec.spl:495/500`, `expect_not` `:503`, `.not_()`
`:512`, all on `ExpectHelper` (`spec.spl:508`). Matchers (all single-shot, no
polling): `to_equal:515`, `to_be:524`, `to_be_true:527`, `to_be_false:535`,
`to_be_nil:543`, `to_be_truthy:551`, `to_be_falsy:559`,
`to_be_greater_than:567`, `to_be_less_than:575`, `to_be_at_least:583`,
`to_be_at_most:591`, `to_contain:599`, `to_start_with:608`, `to_end_with:617`,
`to_be_empty:626`, `to_have_length:635`, `to_be_close_to:644`,
`to_match:656` (substring, not regex). Failures route through
`fail_assertion` `spec.spl:670` (sets `current_test_error`; does not throw).
Standalone asserts: `assert_eq:686` … `assert_contains:718`.

**Caveats (from `.claude/rules/testing.md`):** `to_be_true`/`to_be_false` are
rejected by the runner on bool receivers — use `assert_true`/`to_equal(true)`.
In **interpreter mode the runner only verifies file loading, not `it`-block
execution** — output must be grepped for `✗`, exit codes are not sufficient.
This directly constrains UI test evidence (§7).

### 1.3 Test discovery and runner

- Orchestrator: `src/app/test_runner_new/test_runner_main.spl` (`run_tests`
  `:110`); library: `src/lib/nogc_sync_mut/test_runner/`.
- Discovery: `discover_test_files_fast` `test_runner_files.spl:215`;
  `is_test_file` `:66` matches `*_spec.spl` and `*_test.spl`. Manifest cache
  with `--refresh-manifest` (`test_runner_main.spl:143`).
- System tests must declare `# @cover src/... N%`
  (`validate_system_test_covers` `test_runner_main.spl:163`).

### 1.4 sspec → doc/06_spec generation

- Wired into the runner: `generate_spipe_docs_for_results`
  `test_runner_main.spl:80` shells out to
  `bin/simple spipe-docgen <passing _spec.spl> --output doc/06_spec --no-index`
  (`:84-100`).
- Implementation: `src/app/spipe_docgen/spipe_docgen/parser.spl`
  (`parse_spipe_file` `:32`; annotations `@inline:591`, `@manual:593-621`,
  `@capture:728`, `@prev:876`, `@include:883`, `@step:891/914`) and
  `generator.spl` (markdown manual).
- Canonical template: `.claude/templates/spipe_template.spl` — named step
  helpers (`Then_*` checkers), `describe`/`it` with annotations. Skill:
  `.claude/skills/spipe.md` + `.claude/skills/lib/spipe_ui.md` (the latter
  states the standing rule: **verify the framebuffer, not screenshots**).

### 1.5 Existing polling / auto-wait — std.play (major finding)

`src/lib/nogc_sync_mut/play/` is an existing Playwright-style layer:

- `play/expect.spl` — deadline-polling matchers: `PageExpect` `:24`
  (`to_have_title:31`, `to_have_url:41`), `LocatorExpect` `:54`
  (`to_be_visible:61`, `to_be_hidden:68`, `to_have_text:75`,
  `to_contain_text:85`, `to_have_count:94`); factories `expect_page:107`,
  `expect_locator:110`, `*_with` timeout overrides `:113/116`. Returns
  `Result<(), PlayError>`.
- `play/types.spl` — `DEFAULT_EXPECT_TIMEOUT_MS=5000` `:40`,
  `DEFAULT_ACTION_TIMEOUT_MS=30000` `:41`, `DEFAULT_NAVIGATION_TIMEOUT_MS`
  `:42`, `DEFAULT_LAUNCH_TIMEOUT_MS` `:43`, `DEFAULT_POLL_INTERVAL_MS=100`
  `:44`; `WaitForOptions` `:157`; `ERR_TIMEOUT` `:258`.
- Wait helpers: `play/locator.spl:55` `wait_for`, `play/page.spl:125`
  `wait_for_selector`, `:133` `wait_for_url`;
  `play/sdl2_backend.spl:145` `wait_for_element(widget_id, timeout_ms)`;
  `play/launcher.spl:61` `poll_for_ws_url` (CDP WebSocket readiness).

**Known defects to fix, not re-implement:**
1. Poll loops **busy-spin** — `while now < deadline` with no sleep;
   `DEFAULT_POLL_INTERVAL_MS` is defined but not honored inside the loop.
2. `PlayError` results are **not bridged** into std.spec's
   `fail_assertion`/counters, so play failures don't appear in
   `print_summary`.

### 1.6 Existing snapshot driver — SGTTI

`src/lib/nogc_sync_mut/ui_test/sgtti.spl` — `SgttiTestDriver` `:178` queries a
UI accessibility snapshot (from TUI `UIState` or Draw IR): `click:199`,
`type_text:202`, `check_exists:205`, `check_visible:208`, `check_focused:212`,
`check_enabled:216`, `check_selected:220`, `check_text:224`,
`expect_draw(id, assertion):233`, `find_nodes:196`. **Single-shot** (freshness
via `max_age_ms`), no retry loop. Sibling HTTP driver:
`src/lib/gc_async_mut/ui_test/{client,http,parse,sgtti,types}.spl`.

### 1.7 Existing test API server

`src/app/ui.test_api/` — an HTTP test surface that threads an
`inject_event: fn(UIEvent)` callback: router `handle_test_request`
`handler.spl:44`; `_handle_click` injects `UIEvent.Action("click_{id}")`
`:155-160`; `_handle_type` injects focus + per-char `UIEvent.KeyPress`
`:163-173`; also `_handle_drag`/`_handle_submit`/`_handle_event` `:64-68`.
Mounting: `dispatch_test_api` `mount.spl:26`.

---

## 2. Event-injection mechanisms per lane

### 2.1 GUI lane (hosted WM, `hosted_entry.spl`)

Flow: OS → winit → poll loop → HostCompositor dispatch → WM lifecycle.

- Poll/dispatch loop: `src/os/hosted/hosted_entry.spl:107-160` — calls
  `rt_winit_event_loop_poll_events`, switches on event type:
  `EVT_MOUSE_MOVE` → `comp.pointer_move(mx,my)` (`:122`); `EVT_MOUSE_BUTTON` →
  `comp.handle_left_button(pressed)` (`:130`); `EVT_KEY` → keycode branch
  (`:133-148`).
- Compositor dispatch: `src/os/compositor/host_compositor_entry.spl` —
  `pointer_move` `:322` → `host_compositor_pointer_move` `:525`;
  `handle_left_button` `:342` → `host_compositor_left_button_at` `:546` →
  `wm_lifecycle_left_button` `:578`. Lifecycle logic in
  `src/os/compositor/wm_action_applier.spl`.
- **There is no Simple-side WM event queue** — the winit poll loop drives
  compositor methods directly each frame. The only real queue is Rust-side
  (§2.2).
- **MISSING:** the hosted_entry loop has **no `EVT_MOUSE_WHEEL` branch** —
  wheel events are produced by the runtime but dropped in this lane.

### 2.2 winit runtime queue (Rust seed)

`src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/`:

- Event store: `static EVENTS: LazyLock<Mutex<HashMap<i64, RuntimeEvent>>>`
  `mod.rs:43`; `RuntimeEvent` enum `mod.rs:95` (KeyboardInput, MouseButton,
  MouseMoved, MouseWheel).
- Producer: winit thread converts `WindowEvent`s and does
  `state.event_tx.send(event_value)` `winit_sffi_thread.rs:373` (conversion
  `:350-370`).
- Consumer: `rt_winit_event_loop_poll_events` `winit_sffi_window.rs:48` →
  `event_to_handle` `winit_sffi_thread.rs:377-382` inserts into `EVENTS`.
- **MISSING:** no synthetic-input path. The `UserEvent` proxy (`mod.rs:90`)
  carries only `RuntimeCommand` (window mutations), not input. A
  `rt_winit_inject_event` extern would be net-new **seed** plumbing — and the
  repo policy is seed = bootstrap-only, plus the known dual-handle-table
  hazard (JIT resolves statics from the main binary, interpreter from dylibs)
  makes cross-boundary queue access risky.

### 2.3 OS-level injection

- **Linux — proven:** `scripts/check/check-linux-hosted-wm-live-window-evidence.shs:120-131`
  uses `xdotool search/windowactivate` + `mousemove/click/mousedown/mouseup/key`,
  verified against `[hosted-wm] event mouse_move|mouse_button|key` log markers.
- **macOS — MISSING:** zero hits for `CGEventPost` /
  `CGEventCreateMouseEvent` / `CGEventCreateKeyboardEvent` in `src/`,
  `scripts/`, `tools/`, `bin/`. macOS evidence scripts
  (`check-macos-gui-live-window-evidence.shs:285-300`,
  `check-wm-multiapp-taskbar-evidence.shs:210-245`) use osascript/JXA only for
  frontmost/geometry/window-id and `screencapture` — capture-only, no
  injection.

### 2.4 Web lane — chrome backend

- `bin/codex_chrome_devtools_mcp.cmd` → `bin/codex_chrome_devtools_mcp.js:37-53`
  is a **process-lifecycle wrapper** that spawns the third-party
  `chrome-devtools-mcp` npm package. CDP `Input.dispatchMouseEvent` /
  `dispatchKeyEvent` live in that external package, not in the repo.
- Repo-side CDP readiness polling exists: `play/launcher.spl:61`
  `poll_for_ws_url(stderr_path, timeout_ms)`.

### 2.5 Web lane — Electron

- Renderer→main: `src/app/ui.electron/preload.js` — `sendInput` /
  `ipcRenderer.send('simple-input', envelope)` `:4`; DOM `keydown` `:25`,
  `click` `:35`. Main: `src/app/ui.electron/bridge.js:17` (`ipcMain`),
  forwards to the Simple process.
- WM client transport select: `src/app/ui.web/wm.js:1205-1213` (`_send`,
  electron-ipc vs WebSocket).

### 2.6 Web lane — simple-2d core backend (pure Simple)

- Client emit: `src/app/ui.web/wm.js:1216` `_sendInputEvent(surfaceId,
  widgetId, event)` → `{t:'input_event', …}` frame.
- **Server ingest (the injection point):** `WmBridge.handle_input(surface_id,
  widget_id, event_json, event)` `src/app/ui.web/wm_bridge.spl:61` —
  re-validates `Capability.InputInject` `:69` (also `ui_routes.spl:211`), then
  `pointer_down` → focus dispatch `:82`; `pointer_up` → `UIEvent.Action`
  `:87-89`; `key_down` → `UIEvent.KeyPress` `:91-94`; Tab →
  `FocusNext/FocusPrev` `:99-101`.
- Pipeline accounting already exists: `src/app/ui.browser/backend.spl:305-317`
  (`input_event_enqueued_count`, `…_polled_count`, `…_dispatched_count`,
  `…_pending_depth`, roundtrip timing) — ready-made observability for
  auto-wait ("event settled") semantics.
- winit→DOM translation for browser shells:
  `src/app/ui.browser/event_bridge.spl` / `src/app/ui.chromium/event_bridge.spl`
  (`translate_key_event:53`, `translate_mouse_event:116`,
  `translate_wheel_dom_event:140`).

### 2.7 2D lane (engine2d apps / compositor)

- **Cleanest seam in the repo:** `InputBackend` trait
  `src/os/compositor/input_backend.spl:4-10` (`poll_key() -> KeyEvent?`,
  `poll_mouse() -> MouseEvent?`). Real impl:
  `src/os/compositor/hosted_input_backend.spl` (winit),
  `hosted_input_sdl2.spl:66` (SDL2). Consumer: `Compositor._handle_input_backend()`
  `src/os/compositor/compositor.spl:347` (called from frame loop `:343`;
  field `:27`; wired via `with_backends` `:46`).
- A scripted fake `InputBackend` is consumed identically to real OS input —
  no new plumbing needed.

---

## 3. Capture / assert mechanisms

### 3.1 Pixel readback

- Engine2D: `read_pixels()` `src/lib/gc_async_mut/gpu/engine2d/engine.spl:839`,
  `read_pixels_with_source()` `:852` returning `Engine2DReadback { pixels:
  [u32], source: text }` (`engine2d/backend.spl`). Source values:
  `device_readback`, `cpu_mirror`, `cpu_fallback`, `not_requested`,
  `host_cache_after_device_present`.
- **Silent-fallback gotcha is structural:** plain `read_pixels()` discards
  `source`; `backend_webgpu.spl:529-532` always returns `cpu_mirror`;
  `backend_directx.spl:256-271` silently falls back on empty results. Honest
  consumers must check `source == "device_readback"` — e.g.
  `tools/pixel_compare/render_simple_html.spl:82-91`.
- Engine3D: all backends expose `read_pixels() -> [u32]` (no source variant);
  trait `engine3d/backend.spl:77`; e.g. `backend_software.spl:656`.

### 3.2 Checksums, comparison, golden images

- **Checksum convention** repo-wide: unsigned 32-bit pixel sum
  (`tools/node-render-bitmap/exact_fixture.js:48-54`; awk sums in gates).
  Comparison is **exact** ARGB equality; perceptual metrics are
  diagnostic-only.
- ARGB JSON artifact shape (`tools/pixel_compare/render_simple_html.spl:95-102`):
  `{"width","height","format":"argb-u32","producer","requested_backend",
  "resolved_backend","engine2d_readback_source","gpu_backend_used","pixels"}`.
  Note the O(n)-join JSON build at `:28-40` (per-element push is O(n²) and
  never finished at 320×240).
- **Golden gate exists:** `src/app/wm_compare/golden_gate.spl` — PPM P6
  baselines at `test/03_system/gui/wm_compare/goldens/` (`goldens_dir` `:144`);
  `REGEN_GOLDENS` env `:150`; flow `:163-205`; passes only on
  `pass_exact` (max channel delta 0). Diff engine: `diff_buffers`
  `src/app/wm_compare/backend_parity.spl:428` (`ParityResult` `:28`,
  `pass_exact` `:38`). Also: `test/03_system/engine/game2d_golden_spec.spl`
  with hash baseline `test/fixtures/game2d_golden_hello_720p.hash`.

### 3.3 Evidence-gate scripts

- **63** `*-bitmap-evidence.shs` gates in `scripts/check/`, plus readback and
  parity gates. `evidence.env` = flat `key=value` file, `.`-sourced by shell;
  pass/fail = final shell test on `*_status=pass` keys.
- Canonical examples: `check-macos-metal-browser-backing-evidence.shs`
  (3-way Simple/Chrome/Electron ARGB capture; checksums + pairwise exact diff
  `:111-134`; final gate `:252`);
  `check-metal-generated-2d-readback.shs` (fail-closed per-op checksum cascade
  `:112-152`); `check-shared-wm-renderer-unification-evidence.shs`
  (logic/source-contract gate, not pixels). Shared report lib:
  `scripts/deps/generated-2d-readback-lib.shs`.

### 3.4 Stage logs — DESIGN-ONLY

The `[browser]` stage sequence (`args-parsed` → `backend-resolve-start` →
`backend-selected` → `app-init-done` → `window-create-start` →
`window-created` → `render-frame-start` → `first-layout-done` →
`web-render-html-done` → `pixel-artifact-done` / `first-frame-drawn`) is
documented in
`doc/08_tracking/bug/browser_engine_css_size_quadratic_pixel_render_2026-07-04.md:214-222`
and `doc/08_tracking/bug/ui_browser_main_open_fake_planner_2026-07-05.md:107-116`,
but **grep finds zero emitting code** — only a stale comment at
`src/app/ui.browser/main.spl:76-77`. Implementing the stage tracer is a task
for this infrastructure (it is the designed hang-detection probe); it lands
as a general `std.diag` primitive (design §8).

### 3.5 PPM encoding

- Canonical: `encode_ppm_p6` `src/lib/common/image/ppm_decode.spl:111`; the
  u8-cast marshalling bug is documented in-source at `:116-123` (**never
  `expr as u8` into a `[u8]` destined for extern calls** — store masked ints
  into a pre-sized array, `:144-146`). Decoder `decode_ppm_to_argb` `:57`.
- Second standalone encoder: `src/app/wm_compare/golden_gate.spl:65`.

### 3.6 Existing debug/diagnostics modules (for the shared debug infra)

Inventory relevant to the P0 debug primitives (design §8):

- **Logging (EXISTS, extend):** `src/lib/nogc_sync_mut/log.spl` — reads
  `SIMPLE_LOG` env once at load (near-zero cost off); scope API
  `fatal/error/warn/info/debug/trace/verbose(scope,msg)` `:199-235`; `_emit`
  `:113` → stderr + optional file (`SIMPLE_LOG_FILE_PATH`/`SIMPLE_LOG_DIR`
  `:96-106`), dispatching through `src/lib/log.spl` backend registry
  (`log_register_backend:257`, `RingBackend:292`, `log_dispatch_text:574`).
  Other mut variants are 1-line re-export shims — extend here only.
- **Deadline guard (EXISTS, compose):**
  `src/lib/nogc_sync_mut/failsafe/timeout.spl` — `Deadline` `:109`
  (`remaining_ms`), `check()` `:118`, `TimeoutManager:53`, `TimeoutStats:83`.
- **Perf stats (EXISTS, heavyweight):** `src/lib/nogc_sync_mut/perf.spl` —
  `ComponentStats`/`PerfStats` `:143-217` (benchmark/config-oriented);
  runtime-gated call profiler `io/profiler_simple.spl`
  (`timer_start/timer_end:106/124`).
- **AOP call tracing (EXISTS, separate):**
  `src/lib/nogc_sync_mut/aop_debug_log.spl` — `SIMPLE_AOP_DEBUG`-gated
  enter/exit ring (`debug_log_enter:74`).
- **Interactive debugger (EXISTS, name-collision hazard):**
  `src/lib/nogc_sync_mut/debug.spl` / `debugger.spl` — Debugger/Breakpoint;
  a new module must NOT be called `debug`/`dbg`.
- **Env conventions (EXIST):** `SIMPLE_LOG` (global level),
  `SIMPLE_<SUBSYS>_DEBUG` boolean per subsystem (`SIMPLE_LSP_DEBUG`
  `lsp/transport.spl:58`, `SIMPLE_DAP_DEBUG` `dap/transport.spl:48`,
  `SIMPLE_ACTOR_TRACE` `actor/scheduler.spl:99`).
- **MISSING:** watchdog module (none repo-wide); stage-log helper (§3.4);
  general named-counter registry (the `ui.browser/backend.spl:306-317`
  counters are ad-hoc struct fields); any logging module in `src/lib/common`.

---

## 4. TUI lane

- **Stdlib primitives:** `src/lib/nogc_async_mut/tui/` (`terminal.spl`,
  `style.spl`, `widget.spl`, `layout.spl`, `widgets/*`), re-exported by other
  lanes (`src/lib/gc_async_mut/tui/__init__.spl:1`).
- **App framework:** `src/app/ui.tui/` — `screen.spl`, `backend.spl`,
  `input.spl`, `async_app.spl`, `standalone.spl`; shared primitives in
  `src/app/ui.render/` (`ansi.spl`, `tui_widgets.spl` `render_tui_tree`, …).
- **Output capture — string buffer, no pty needed:** `Screen.render() -> text`
  `src/app/ui.tui/screen.spl:449` (impl `screen_render` `:453`) emits the full
  ANSI frame as a string; `Screen.buffer: [text]` `:184`; ANSI-aware width
  math `_split_visible`/`_visible_len` `:89-178`. The normal path prints it
  (`TuiBackend.render` `backend.spl:67-81`) — tests call `screen.render()`
  directly. Alternative structured captures: semantic snapshot
  `tui_semantic_snapshot` `backend.spl:131`; HTML projection
  `src/app/ui.tui_web/screen_to_html.spl`.
- **Input:** `parse_input_line -> UIEvent` `src/app/ui.tui/input.spl:13`
  (line-based today, `:3-5`); raw-mode hooks `rt_term_read_timeout`/`rt_term_poll`
  `input.spl:91-92`, `poll_raw_input` `:94`; `TuiBackend.poll_event`
  `backend.spl:90`. **Synthetic injection seam already exists:** the
  `inject_event: fn(UIEvent)` callback threaded through
  `src/app/ui.test_api/handler.spl:44` (§1.7).
- Pty capture was researched previously
  (`doc/01_research/ui/terminal/TERMINAL_SEQUENCE_CAPTURE.md`) — a
  portable-pty approach for testing the REPL through a real terminal; that
  remains the right tool for *terminal emulator* fidelity but is unnecessary
  for widget-tree TUI tests given `Screen.render()`.
- Existing TUI apps to test against: `src/app/editor/tui_main.spl` (+
  `tui_shell*.spl`), `src/app/svim/tui_shell.spl`, `src/app/terminal/main.spl`,
  `src/app/ui.tui/standalone.spl`.

---

## 5. 3D — honest assessment

**engine3d exists and works, CPU-only.** Location:
`src/lib/*/gpu/engine3d/`:

- `Engine3D.create(w,h)` `engine3d/engine.spl:61`; `set_camera` `:126`;
  `clear`/`clear_depth` `:136/139`; `submit_triangle` `:146`;
  `read_pixels()` `:199`; primitives `draw_cube/draw_sphere/draw_plane/…`
  `:215-227`; `draw_wireframe` `:237`; `submit_indexed_mesh` `:244`.
- `Camera3D.perspective` `camera3d.spl:41`, `orthographic` `:56`;
  `SceneNode3D` `scene_graph3d.spl:7`, `SceneGraph3D` `:79`.
- Real depth-tested scanline rasterizer: `backend_cpu.spl` (`depth: [f32]`
  `:111`, triangle fill `:269/:422`).
- **All non-CPU engine3d backends are software-fallback stubs** — e.g.
  `backend_metal.spl:7-11` states native Metal submission is future work;
  `engine.spl:6` "cpu (only backend for now)".
- Demo: `src/app/model3d/main.spl`.

Consequence: 3D output is deterministic CPU pixels — testable with exactly the
same `read_pixels()`/checksum machinery as 2D. Hardware 3D is deferred, the
*testing seam* is not.

Engine2D reference: facade `engine2d/engine.spl` (`create:110`; backend
priority `:6/:113`; **`SIMPLE_2D_BACKEND` env override `:57-62`** — force
`cpu`/`software` for deterministic CI); draw trait `backend.spl:25-47`;
extended API `backend_adv.spl:32-72`.

---

## 6. Playwright concepts and what transfers

From knowledge of Playwright's architecture (no web fetch needed):

| Playwright concept | What it is | Transfers? |
|---|---|---|
| Locator model | `page.locator(sel)` is a lazy *query description*, re-resolved at each action/assert — never a stale element handle | **Yes, core.** Resolves per-lane: SGTTI snapshot query (tui/gui), CSS via CDP (web-chrome), DOM/layout-tree query (web-simple-2d), region/name registry (2d/3d). `play/locator.spl` already models this. |
| Auto-wait actionability | Every action waits for visible ∧ stable (not animating) ∧ enabled ∧ receives-events, up to timeout | **Yes.** Poll the same snapshot the locator resolves against; "stable" = same bounds across two consecutive frames. |
| Web-first assertions | `expect(locator).to_have_text(…)` polls until pass or deadline | **Yes** — `play/expect.spl` already does this; needs sleep-based polling + std.spec bridging (§1.5 defects). |
| Timeout = failure with trace | Timeouts produce a rich artifact (trace/snapshot), not just "timed out" | **Yes** — repo analog: dump stage log (§3.4, to be implemented), SGTTI snapshot, and last frame checksum on TIMEOUT. This is the hang detector. |
| Frozen clock | `page.clock.install()`, `clock.tick(ms)` — virtual time for animation tests | **Yes, must be designed** — nothing exists; frame loops read wall-clock today. |
| Trace viewer | Recorded screenshots+DOM per action | Partial — per-action frame checksums + optional PPM dumps; full traces deferred. |
| Browser contexts/isolation | One browser, many isolated contexts | Partial — repo analog is one app process per test session; contexts deferred. |
| Codegen/recorder | Record user actions into a script | Out of scope. |

---

## 7. Gaps table

Legend: cell = where it exists today, or **MISSING**. "dispatch-level" means a
seam above the OS queue (acceptable, but must be labeled in evidence).

| Lane × capability | launch | locate | inject | assert-state | assert-pixels | clock control | teardown |
|---|---|---|---|---|---|---|---|
| **TUI** | `ui.tui/standalone.spl`, `async_app.spl` (in-process) | SGTTI `sgtti.spl:196` over `UIState` | `inject_event` cb `ui.test_api/handler.spl:44` | `Screen.render()` string `screen.spl:449`; semantic snapshot `backend.spl:131`; SGTTI checks | n/a (text cells = the pixels) | **MISSING** | process/loop exit only, no session API |
| **GUI (hosted WM)** | `hosted_entry.spl` via `bin/simple run` (interpret mode) | SGTTI over Draw IR (`sgtti.spl`), window list in compositor | dispatch-level: `pointer_move:322`/`handle_left_button:342`; OS-level Linux `xdotool`; **MISSING:** wheel branch, macOS CGEvent, winit-queue inject | `[hosted-wm] event …` log markers; SGTTI | `read_pixels_with_source` `engine.spl:852`; golden gate `golden_gate.spl`; evidence.env gates | **MISSING** (wall-clock frame loop) | kill process; no graceful session close |
| **Web (chrome)** | `play/launcher.spl` (CDP ws poll `:61`); `codex_chrome_devtools_mcp.js` wrapper | CSS via external chrome-devtools-mcp; `play/page.spl` selectors | CDP Input.* — external package only; **MISSING** in-repo CDP input client | `play/expect.spl` polling matchers | `tools/chrome-live-bitmap/capture_html_argb.js`; ARGB JSON gates | **MISSING** (CDP Emulation.setVirtualTimePolicy unused) | launcher kill |
| **Web (simple-2d)** | `ui.browser`/`ui.web` server via `bin/simple run` | widget_id in DOM/layout tree; SGTTI | `WmBridge.handle_input` `wm_bridge.spl:61` (Capability-gated) | input pipeline counters `ui.browser/backend.spl:305-317`; session state | presenter readback `simple_web_html_engine2d_presenter.spl:19-30`; ~6 min/frame full-page (filed bug) | **MISSING** | ws close / process kill |
| **2D (engine2d)** | in-process `Engine2D.create` `engine.spl:110` | **MISSING** (no widget tree — needs region/name registry) | fake `InputBackend` via `with_backends` `compositor.spl:46` | compositor state fields | `read_pixels_with_source:852`; `SIMPLE_2D_BACKEND=cpu`; goldens | **MISSING** | in-process drop |
| **3D (engine3d)** | in-process `Engine3D.create` `engine.spl:61` | **MISSING** (scene-node names exist `scene_graph3d.spl:7` but no query API) | n/a today (no interactive 3D app) | scene graph state | `read_pixels` `engine.spl:199` (CPU-deterministic) | **MISSING** | in-process drop |

Cross-cutting missing pieces:
1. **Unified session API** (`UiTest.launch(lane, app, opts)`) — nothing ties
   the lanes together.
2. **Virtual clock** — all frame loops are wall-clock.
3. **Stage logs** — designed, not implemented (§3.4).
4. **Sleep-based polling + std.spec bridge** in play/ (§1.5).
5. **Wheel** in hosted WM loop; **macOS OS-level injection**; **in-repo CDP
   input client**.
6. **Region/name locator registry** for 2d/3d.
7. **Debug primitives** — watchdog, stage tracer, counters registry (§3.6).

## 8. Filed bugs and constraints that shape the design

- Web full-page pixel render ≈ 6 min/frame — quadratic CSS
  (`doc/08_tracking/bug/browser_engine_css_size_quadratic_pixel_render_2026-07-04.md`);
  fix in flight but design must not assume it.
- JIT panics on winit — GUI/graphics require `SIMPLE_EXECUTION_MODE=interpret`.
- Interpreter runner verifies file loading, not `it`-block execution
  (`.claude/rules/testing.md`) — evidence gates must grep output.
- Interpreter TCP write-after-read bug blocks tight WS loops (memory:
  `project_ui_web_nav_and_tcp_bug`) — affects a pure-Simple CDP client.
- `[u8]` `as u8` push marshalling bug (`ppm_decode.spl:116-123`).
- `index_of` misses brace needles / chained-replace hazards (memory:
  `bug_index_of_brace_needle`) — affects selector parsing code.
- Dual handle-table (JIT statics vs dylib statics) — makes cross-boundary
  winit-queue injection from a cdylib unreliable; seed changes are
  bootstrap-only policy.
- play/ busy-spin polls; `to_be_true`/`to_be_false` runner rejection.
