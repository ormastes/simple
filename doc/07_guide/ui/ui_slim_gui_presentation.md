# UI-slim G0/G1 GUI presentation gate

How the ui_slim lane proves it can put a **real, displayed OS window** on screen,
and how the G1 presentation latencies are measured. Verified on macOS arm64
(2026-09-06). TL;DR: `ui_slim_gui_presentation_tldr.md`.

## Run it

```bash
sh scripts/check/check-ui-slim-gui-present.shs [--out /abs/path/g1.ppm]
sh scripts/check/check-ui-slim-gui-present.shs --selftest    # -> selftest: 4/4 passed
```

The check always selftests first; a selftest failure is `ERROR`, never a pass.

## Route and binary — no new plumbing

The fixture `test/05_perf/ui_slim/g1_greeting_gui.spl` uses the route that
already exists, exactly as `src/app/ui_showcase/hosts/main_gui.spl` does:

```
common.ui.builder  column(label "Hello from Simple UI!", button "Click me")
  -> build_tree_with_title -> UIState
  -> common.ui.widget_draw_ir.widget_tree_to_draw_ir      (DrawIR v2)
  -> common.ui.draw_ir_v2_to_v3.draw_ir_v2_to_v3_with_ids (v3 scene)
  -> app.ui_showcase.hosts.host_gui.ScreenGuiHost.present_scene
  -> nogc_sync_mut.ui.gui_renderer.GuiRenderer.present_argb_u32
  -> dlopen build/sffi/libspl_winit.<dylib|so|dll> (winit + softbuffer cdylib)
```

Nothing is hand-drawn with raw engine2d primitives, and no renderer, host or
driver source is modified — the fixture and the check script are additive.

Launch is `scripts/gui/macos-gui-run.shs`, which copies a **GUI-enabled** driver
into a throwaway `.app` so LaunchServices registers the process in the Aqua
session; a bare CLI process never composites. That script picks the driver by
grepping it for `rt_winit_event_loop_new`. On this host the only binary carrying
that marker is `bin/release/aarch64-apple-darwin/simple` (2026-07-25) — the Rust
**seed** at `src/compiler_rust/target/bootstrap/simple` does **not** carry it and
is refused by name (`is_rust_seed_simple`). No compiler is built by this gate.

### The two environment prerequisites

1. `build/sffi/libspl_winit.dylib` must exist. A prebuilt one ships at
   `src/runtime/spl_winit/target/release/libspl_winit.dylib`; copy it. Absent,
   the fixture reports `no_window` and the gate FAILs (correctly).
2. `open -n` gives the child cwd `/` and forwards only the `LSEnvironment` keys
   in the generated `Info.plist`. `SIMPLE_SPL_WINIT_PATH` is **not** one of them
   and GuiRenderer's other candidate is the relative `build/sffi/...`, which
   cannot resolve from `/`. `DYLD_LIBRARY_PATH` **is** forwarded, and dyld
   consults it with the dlopen leaf name, so the check exports
   `DYLD_LIBRARY_PATH=<repo>/build/sffi`. That is why the check sets it and why
   the route script needs no edit.

## Milestones and the clock

The fixture writes to **stderr**, one line each:

```
[ui-slim] probe size=WxH bg=RRGGBB rect=x,y,w,h btn=cx,cy
[ui-slim] entry|window_created|first_frame_submitted|input_ready|input_response t_ns=<ns>
[ui-slim] hold_complete|exit_ok t_ns=<ns>
```

`t_ns` is `time_now_unix_micros() * 1000` — **CLOCK_REALTIME, microsecond
resolution, not monotonic**. The check stamps `t0` with the same clock
immediately before launching (`gdate +%s%N`, else `python3 time.time_ns()`, else
`date +%s` at second resolution; the chosen one is printed as `clock:`). Both
sides therefore share a clock; a wall-clock step during a run invalidates the
numbers. It reports, with `NOT_MEASURED` for any absent milestone:

`launch_to_entry`, `launch_to_window_created`, `launch_to_first_submission`,
`launch_to_input_ready`, `input_to_visible_response`.

`input_to_visible_response` is a **synthetic** activation: the button centre from
`compute_layout`/`find_rect` is fed through the real `widget_dispatch_click`, the
greeting label is rewritten, and the next scene is presented. Deterministic; no
osascript, no fabricated event.

After `--hold-ms` (default 500) of continuous re-presentation — macOS blanks a
window that only redraws on dirty — the fixture shuts the host down and exits 0.

## Oracle: the framebuffer, never a screenshot

`--out` receives a binary P6 PPM built by `raster_to_ppm_bytes` over the exact
`[u32]` buffer handed to `present_argb_u32` (`raster_scene_argb` on the presented
scene). The check reads the PPM directly and requires, inside the greeting rect
the fixture declared:

* at least one pixel differing from the declared background, **and**
* at least **2 distinct colours** — a flat non-background block is a painted
  panel with no glyphs on it and FAILs.

A screen capture is never accepted: it can grab whatever window happens to sit at
those coordinates.

## Verdicts

Last line of stdout, exit code alongside:

| verdict | exit | meaning |
|---|---|---|
| `PASS — window presented, <k> milestones, ppm non-blank` | 0 | a window was created and its framebuffer carries content |
| `FAIL — ...` | 1 | launched, but no `window_created`, no/blank/flat PPM, or a present failure |
| `ERROR — nothing was checked (...)` | 2 | selftest failed, fixture missing, or the route produced no bundle |

A zero-exit run with no `window_created` milestone is **FAIL**, never a pass. A
headless counter, a `gui_dynlib_hot_probe_tick`, or a screenshot is never a
substitute for a displayed window.

`--selftest` builds four fake fixtures and asserts the documented verdict for
each: all milestones + non-blank PPM → PASS; milestones + blank PPM → FAIL; no
`window_created` → FAIL; missing fixture → ERROR. It prints `selftest: 4/4
passed`.

## Measured 2026-09-06 (macOS arm64, driver `bin/release/aarch64-apple-darwin/simple`)

```
launch_to_entry             5400.9 ms
launch_to_window_created    5694.8 ms
launch_to_first_submission 10428.3 ms
launch_to_input_ready      12698.8 ms
input_to_visible_response   2726.3 ms
ppm 240x140, greeting_rect=1,1,238x69, bg=#141414, sampled=16422 differing=16422 distinct=2
PASS — window presented, 5 milestones, ppm non-blank
```

These are **interpreted** figures (`SIMPLE_EXECUTION_MODE=interpret` is forced by
the route's `Info.plist`) at a deliberately small 240x140. They are a
presentation-path baseline, not a G1 target: the ~5.4 s to `entry` is interpreter
startup over `SIMPLE_LIB=src`, and the ~4.7 s from window to first submission is
interpreted rasterisation. Scale the window with `--w`/`--h` only with that cost
curve in mind — `main_gui.spl` records that a full 528x692 first frame takes tens
of minutes interpreted, which would exceed the 30 s watchdog.

## Diagnostics that are NOT failures of this gate

* `WARNING: this Rust-built Simple binary is a bootstrap seed only` — provenance
  note from the selected driver.
* `compiler_cross_module_private_symbol_collision` warnings for `_emit`,
  `env_get`, `shell`, `process_wait`, … — pre-existing co-compilation warnings
  from the stdlib closure, not introduced here.
* `[memory-guard] SIMPLE_LIB=... contains 600+ .spl files` — advisory.
* `fn exit ... shadows the prelude builtin` — a stdlib shadow, advisory.
* Exit 141 from `macos-gui-run.shs` — that script's own `ps | awk` pid lookup can
  die on SIGPIPE under `pipefail` **after** `open` already succeeded. The check
  recovers the bundle from the route's `launching ...` line and continues; only a
  launch that produced no bundle at all is ERROR. (Route-side defect; not fixed
  here because this work package is read-only on that script.)

## Rerunning for certification

The gate is self-contained and re-entrant: it selftests, records its own
external timestamp, kills the app after `UI_SLIM_TIMEOUT_S` (default 30 s) so no
window is left open, and cleans its work directory. Certification reruns
`sh scripts/check/check-ui-slim-gui-present.shs --out <artifact>.ppm` on a macOS
host **with a display and an unlocked session** (a headless or locked session
yields `no_window`, which is FAIL, not a skip), keeps the printed milestone table
and the PPM as the artifact pair, and requires the last line to be `PASS`.
Knobs: `UI_SLIM_TIMEOUT_S`, `UI_SLIM_HOLD_MS`, `SIMPLE_SFFI_DIR`,
`UI_SLIM_LAUNCHER` (selftest injection only — the real route is the default).
