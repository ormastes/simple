# GUI Showcase Launch Evidence — standalone + in-WM (2026-07-06)

Evidence-only run on the MAIN working copy (`/Users/ormastes/simple`), zero source edits.
Host: Yoons-MacBook-Air, arm64, macOS 25.5.0. WC tree sha `ed0eaad395fe15ba0f33b19d9338b27e8ddb1c57`.
Artifacts: `build/showcase-evidence/` (+ `INDEX.md`).

## Environment / launch mechanics
- Default binary `bin/simple` -> `release/aarch64-apple-darwin-macho/simple` (self-hosted; **no winit symbol**, headless only).
- Winit GUI driver: `src/compiler_rust/target/gui/debug/simple` (debug build; **release GUI driver missing**). Used by `scripts/gui/macos-gui-run.shs`, which wraps the driver in a throwaway `.app` bundle so LaunchServices registers it.
- All runs `SIMPLE_EXECUTION_MODE=interpret SIMPLE_LIB=src` (JIT panics on winit/graphics — guide mandate). `run` example-timeout raised via `SIMPLE_TIMEOUT_SECONDS`.
- Targets: (1) `examples/06_io/ui/widget_showcase_gui.spl` (canonical standalone, CPU lane); (2) `examples/06_io/ui/wm_widget_showcase_gui.spl` — **peer-modified uncommitted** in WC (diff captured in `wm_showcase_wc_diff.txt`: adds `ChildFrame`/`ChildLocalHit` structs + `fill_rect_pixels`/`draw_taskbar_pixels` pixel-compositing). Both files pass `bin/simple check` (exit 0).

## Per-lane launch commands + results
| Lane | Command | Result |
|------|---------|--------|
| Standalone headless render | `SHOWCASE_PPM=… bin/simple run widget_showcase_gui.spl` | PASS — 520x660 PPM, exit 0 |
| Standalone synthetic events | `SHOWCASE_EVENTS=… SHOWCASE_BEFORE_PPM=… SHOWCASE_AFTER_PPM=… bin/simple run …` | PASS — all region asserts pass, exit 0 |
| Standalone real window | `SIMPLE_GUI_RUN_SKIP_NUDGE=… macos-gui-run.shs widget_showcase_gui.spl` | RENDER PASS (window composited on-screen, `standalone_screen.png`); live-input BLOCKED (see Blockers) |
| WM-client bridge (headless half) | `SIMPLE_WM_APP_MODE=client SIMPLE_WM_BRIDGE_FILE=… SIMPLE_WM_FRAME_FILE=… bin/simple run widget_showcase_gui.spl` | PASS — frame + bridge `create_window` + state written, exit 0 |
| WM host real window | `macos-gui-run.shs wm_widget_showcase_gui.spl` | BLOCKED — no observable output/child frame under parallel-agent load (same winit registration + stdout-capture flakiness) |
| WM unification gate | `SIMPLE_BIN=bin/simple scripts/check/check-shared-wm-renderer-unification-evidence.shs` | RED (`logic-check-failed`) — but runtime test 4 examples / 0 failures; root-caused below |

## A. Rendering
| Metric | Standalone (headless) | Standalone (on-screen) | WM-client (fs bridge) |
|--------|----------------------|------------------------|-----------------------|
| Dims | 520x660 (343200 px) | 520x660 window, retina display | 520x660 (scale 1) |
| Nonblank | 45760 px = **13.33%** (vs BG 0x14141C) | full widget gallery visible | identical frame |
| Framebuffer md5 | `d8041a704e12d28466da1f4901681663` | (visual, `standalone_screen.png`) | `d8041a70…` (**identical → same source proven**) |
| Backend / provenance | `software; requested=software` (CPU lane) — no GPU claim, no read_pixels fallback ambiguity | window-server composite | in-process encode |
| First-frame time | ~6.4 s (release, interpret; startup-dominated) | ~21–38 s (debug driver + .app) | ~6 s |

- On-screen render **proven** (`standalone_screen.png`): real macOS window titled "Simple Widget Showcase (CPU lane)", SimpleGui frontmost, all 24 widgets (Button/Clicks 0, Checkbox/Radio, Toggle, Text input, Dropdown, Progress 62%, Slider, Search, Tabs, Segmented, List, Table, Tree, Card, Badge/Chip, Tooltip, Dialog, Scrollbar, Avatar).
- Debug GUI driver headless render md5 identical to release (`gui_driver_render.ppm`) — same frame across binaries.
- **No Metal/GPU lane exercised** for this target — `widget_showcase_gui.spl` is CPU-lane only; `widget_showcase_metal_gui.spl` exists but was not the guide target. So no `device_readback`-vs-mirror provenance was needed (nothing claimed as GPU).

## B. Event handling (synthetic-event region-scoped oracle — asserts STATE CHANGES)
Offscreen event mode applies each event through the real handler (`apply_showcase_event`/`showcase_on_pointer`) and asserts the framebuffer changed **only** inside the targeted widget cell.

| Injected event | Observed delta (px changed in target cell) | Region | Pass/Fail |
|----------------|--------------------------------------------|--------|-----------|
| `click:button` (counter++) | **1099** | (12,46,254,66) | PASS |
| `toggle:switch` | **544** | (12,112,254,66) | PASS |
| `advance:progress` (+20) | **266** | (12,244,254,66) | PASS |
| outside-region invariant | **0** | whole frame minus cells | PASS |
| overall | 3/3 events | — | PASS (exit 0) |

- `events_before.ppm` md5 `d8041a70…` vs `events_after.ppm` md5 `ab7e7abe690c2d10c21c4cdfe0bcf640` — before/after framebuffers differ (state changes rendered).

**Real OS input (live window, CGEvent via cliclick):**

| Injected event | Observed state delta | Pass/Fail |
|----------------|----------------------|-----------|
| Titlebar drag: press (460,135) → move → release (610,215), delta (+150,+80) pts | Window-server bounds **(200,120) 520x692 before AND after → delta (0,0)**; window LOST frontmost — mouse-down routed to the occluded window behind (menu bar SimpleGui→Terminal) | **FAIL — expected today.** Becomes the regression test for the #25 fix. Evidence: `drag_before.png`, `drag_after.png`, `drag_after_windowlist.txt` (CGWindowList), `drag_test.txt` |
| Button click / text echo / wheel / arrows (live) | not deliverable — same input-routing failure | BLOCKED |

- User-confirmed symptom (matches): window cannot be dragged, no interaction lands.
- **Bug filed:** `doc/08_tracking/bug/gui_winit_window_not_registered_window_server_2026-07-06.md` (severity HIGH; root-cause direction: missing NSApplication activation policy Regular + activate before first map in the CLI-spawned GUI driver; fix owned by GuiRenderer/spl_winit, task #25).
- The event-handling *logic* is proven above; what is unproven is a real winit-delivered click driving `button_count` in a live window.

## C. Animation
Live-window fps could **not be measured** (live-window lane blocked). Designed cadence read from source (`widget_showcase_gui.spl`):
- Present loop `thread_sleep(30)` (line 871) → **~33 fps ceiling**; re-render only when `dirty` (line 864).
- Progress animation `showcase_on_tick` every `500000 µs` (lines 860–861) → **2 Hz** progress increment (`progress = (progress+2) % 101`, lines 106–109). Confirmed statically at 62% in `standalone_screen.png`.
- 4K/8K perf probes (200 frames) are **impractical in interpret mode** (>2 min wall, timed out) — and JIT is unavailable for graphics, so no compiled-lane fps figure. No frame-time median/p95 obtainable without the live lane.

## D. Performance
| Metric | Value | Source |
|--------|-------|--------|
| Cold start → first frame (standalone, release, interpret) | 6721 / 6377 / 6272 ms → **median 6377 ms** | `cold_1..3_time.txt` |
| Peak RSS (standalone) | 359.8 / 360.1 / 360.0 MB → **~343 MiB** | `/usr/bin/time -l` |
| Frame determinism | 3/3 identical md5 `d8041a70…` | `cold_*.ppm` |
| Debug GUI driver headless startup | **21.4 s** (3.3× release) | `gui_driver_render.out` |
| WM-client cold start (headless) | ~6 s | `wm_client_bridge.out` |
| 4K perf probe (200 frames @ 3840x2160) | **impractical** — >120 s, killed | `perf_4k.out` (empty) |
| CPU% idle vs animating | not sampled — live window lane blocked | — |
| Event→render latency | logic-only (synthetic re-render immediate); live latency blocked | — |

## Standalone vs in-WM comparison
| Dimension | Standalone | In-WM | Overhead |
|-----------|-----------|-------|----------|
| Render source | direct Engine2D CPU lane | **same source** spawned as child process, frame written to fs, WM composites chrome + child blit | +1 process + fs bridge round-trip |
| Frame md5 | `d8041a70…` | child frame `d8041a70…` (identical) | 0 (bit-identical child frame) |
| Cold start (headless-comparable) | 6.4 s | ~6 s child | ≈ equal (child ≈ standalone) |
| On-screen present | winit window (blocked for input) | WM host winit window + titlebar chrome | WM adds compositor + child-spawn; real-window present blocked for both (same winit registration issue) |
| Renderer-unification logic | n/a | test **4 examples / 0 failures**, `host_source_contract=pass` | — |

Bounded-overhead quantification of the WM live present vs standalone live present was **not** obtainable because both live-window lanes hit the same window-server registration blocker; the *headless* child (WM-client) is bit-identical and ~equal cost to standalone.

## Blockers (exact)
1. **Live real-OS-input on the on-screen window — BLOCKED.** The winit window from the debug GUI driver *composites and is visible* (`standalone_screen.png`), but the process does **not register in the macOS accessibility/window-server layer** such that it can be programmatically raised/positioned/targeted:
   - System Events finds no process by name `"SimpleGui"` nor by `unix id` (`osascript` returned "no process for pid …") though `ps`/`pgrep` show it alive.
   - The launcher nudge (`scripts/gui/macos-gui-run.shs:93-111`) references `application "SimpleGui"` / `processes whose name is "SimpleGui"` — silently no-ops, so the window is not reliably raised/positioned; under parallel-agent load it sits behind other windows.
   - computer-use `request_access(["SimpleGui"])` → denied `not_installed` (throwaway bundle id `com.simple.gui.run.$$` in `/var/folders`, not LaunchServices-installed) → screenshot/click filtered out.
   - Consequence: CGEvents at the window's own rect are routed to the window BEHIND it (proven by the drag test: bounds delta (0,0) + frontmost lost). `CGWindowListCopyWindowInfo` DOES list the surface (`onscreen=true, layer=0`) — the compositor knows the window; the Aqua session does not know the app (no activation policy / AX registration).
   - **Filed as** `doc/08_tracking/bug/gui_winit_window_not_registered_window_server_2026-07-06.md` (HIGH). Root-cause direction: set NSApplication activation policy **Regular** + `activate` before first window map in the winit runtime (GuiRenderer/spl_winit, task #25); then make the launcher nudge PID-based instead of name-based. Related: `doc/08_tracking/bug/macos_winit_window_not_displayed_2026-05-28.md`.
2. **WM unification gate RED — two independent causes** (`scripts/check/check-shared-wm-renderer-unification-evidence.shs`):
   - **Parser (check frontend):** `bin/simple check` fails to parse SPipe block headers in `test/03_system/app/ui/feature/shared_wm_renderer_unification_spec.spl` — "unexpected token in expression: ':'" at `75:60` (`describe "…":`), `76:90`, `103:84`, `129:77`, `143:82` (`it "…":`). The **same file runs fine under `bin/simple test`** (4 examples, 0 failures), so `check` and `test` use divergent frontends. The app files themselves pass `check`; the gap is SPipe `describe/it` block syntax in the `check` path.
   - **Script false-negative:** the script marks `logic_test_status=fail` because it greps `test.out` for JSON `"success": true` (line 106) but the runner emits human format ("4 examples, 0 failures") — `--format json` not honored. `host_source_contract_status=pass`, `boolean_wrapper_scan_count=0`. Proposed fix: (a) fix the `check` parser for `describe/it` block headers OR use `test`-only gating for specs; (b) make the script parse the runner's actual output (or pass a JSON-emitting flag the runner honors).
3. **4K/8K perf probes impractical in interpret mode** — 200 frames at 3840x2160 exceed 2 min; JIT can't be used (graphics panic), so there is no compiled-lane fps/percentile figure for animation/perf. Proposed fix: add a native-resolution (520x660) headless perf-probe env knob so throughput is measurable without JIT, or fix JIT graphics so the compiled lane is usable.
4. **Release GUI driver missing** — only `src/compiler_rust/target/gui/debug/simple` exists (debug, 3.3× slower startup). Proposed: build+deploy a release GUI driver (`CARGO_TARGET_DIR=target/gui cargo build -p simple-driver --features gui --release`) for representative live-lane timings.
