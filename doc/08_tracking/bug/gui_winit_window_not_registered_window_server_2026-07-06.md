# BUG: winit GUI window composites but is not registered with the macOS window server / accessibility layer

- **Date:** 2026-07-06
- **Severity:** HIGH — blocks ALL live GUI interaction on macOS (clicks, typing, drag, programmatic control)
- **Status:** closed (2026-09-17 live re-verification — window registration, drag, and input routing all PASS; see the Closed section)
- **Area:** GUI / winit runtime / macOS launch path
- **Fix owner:** GuiRenderer / spl_winit work (task #25)
- **Related:** `doc/08_tracking/bug/macos_winit_window_not_displayed_2026-05-28.md` (predecessor: window not displayed at all; this bug is the residue after the .app-bundle workaround makes it display)

## Closed 2026-09-17 — re-verified live on macOS

Supersedes the interim "partially resolved, kept OPEN" verdict in the
`2026-09-17 re-verification (macOS sweep)` section below (that sweep stopped
before the window phase; this run went end-to-end). All three recorded PASS
criteria met, live on macOS 25.5.0 (Apple M4, 2x display). Evidence:
`build/showcase-evidence/2026-09-17-reverify/` (`ix_*` files = the passing
run; `run*-launch.*`, crash logs, captures = the preceding failed attempts).

**1. AX registration — PASS.** `System Events` finds process "SimpleGui" and
`count windows` ≥ 1 (`ix_bounds_before.txt` written while count=1; the sweep
section below has the process-name query). `lsappinfo metainfo` lists
`"SimpleGui" ASN:0x0-0x2c42c4` in `bringForwardOrder`.

**2. Titlebar CGEvent drag — PASS.** Window set to {200,120}; cliclick
`dd:330,127 w:300 dm:400,167 dm:480,207 w:200 du:480,207` (the recorded
cadence and recorded (+150,+80) delta; start moved from 460,130 → 330,127
because AX reports the 520x660-px window as 260x362 **points** on this 2x
display). System Events bounds: `bounds_before=200120 size=260362` →
`bounds_after=350200 size=260362` — delta exactly (+150,+80), versus the
2026-07-06 baseline of (0,0). Screencaptures: `ix_before.png`,
`ix_after.png` — real window with traffic lights and title
`gui_showcase_backed_…`, composited on screen, frontmost throughout.

**3. Click + input routing — PASS (with a stated adaptation).** Titlebar
click at the post-drag position → `frontmost_after_click=true` (menu bar
shows "SimpleGui"). `cliclick t:q` → the app consumed key code 81
(`keycode_to_simple(KeyQ)=81`, matching `showcase_should_close`) and exited
cleanly: `alive_after_q=false`, final stdout flushed in
`run8-final-launch.out`. The literal "Clicks counter + `[widget-showcase]
input left_button` log" form cannot fire in this example revision: `main()`'s
GUI loop polls input but only acts on close/keys, and `apply_native_input`
(the counter/print path) is not wired into it (pre-existing example defect,
unrelated to this fix). Frontmost-flip plus key-consumed exit is delivery
proof through the same CGEvent → WindowServer → winit runtime path the
recorded criteria target.

**Run command (same launcher, same repaired-copy stimulus):**

```sh
SIMPLE_TIMEOUT_SECONDS=3600 SHOWCASE_RESOLUTION=520x660 \
SIMPLE_GUI_BINARY=$PWD/build/showcase-evidence/2026-09-17-reverify/simple-gui-driver-release \
scripts/gui/macos-gui-run.shs \
$PWD/build/showcase-evidence/2026-09-17-reverify/widget_showcase_gui.spl
```

**Required deviations (each forced by a defect outside this bug's scope; the
sweep section below covers the first two):**

- Repaired example copy (tracked file has 5 half-landed symbols —
  `showcase_resolution_wh`, `sc1`, `showcase_on_tick`,
  `showcase_gpu_backend_requested`, dropped `Engine2D` import,
  `ShowcaseState` fields; see Gap 2 in
  `toolchain_gaps_exposed_by_wm_web2d_retained_perf_gate_2026-09-17.md`).
- Driver pinned via `SIMPLE_GUI_BINARY`: `bin/simple` (bootstrap, Sep-14
  14:24 JST) predates the fix commits (Sep-14 21:35 JST) yet wins the
  launcher's marker probe — running the recorded command verbatim would test
  unfixed code. Passing driver: release-profile `simple-driver --features
  gui` + `-Wl,-stack_size,0x4000000` (GUI mode runs on the 8 MB real main
  thread; the showcase recursion overflows it — see `run2-launch.err`), plus
  a rebuilt `build/sffi/libspl_winit.dylib` (the staged one was Sep-6,
  pre-fix) and `launchctl setenv SIMPLE_SPL_WINIT_PATH` (launcher plist does
  not pass it). Both launchctl vars unset after the run.
- `SIMPLE_TIMEOUT_SECONDS=3600` instead of the recorded 200: the driver's
  general wall-clock watchdog (`driver/src/cli/init.rs`) starts at process
  spawn, and the interpreted mainline takes ~10+ min in GUI mode before the
  window maps; 200 s kills it pre-window (`run3/run5-watchdog-crash.log`).
- **AX flapping:** while the interpreted mainline holds the main thread,
  System Events intermittently reports 0 windows / -1719 and the window
  server lists no WindowID; the window is stable once the present loop runs.
  The passing interaction therefore chained catch → position → bounds →
  capture → cliclick drag → bounds → capture → click → frontmost → type-q
  in ONE AppleScript transaction (`/tmp/sginteract.scpt`) so no probe could
  land in a gap. Interactive use post-startup is normal.

## 2026-09-17 re-verification (macOS sweep)

Live re-run of this record's repro on macOS 25.5.0 (Apple M4), gui-feature
seed debug binary (`src/compiler_rust/target/gui/debug/simple`, built
2026-09-17), launched through proper `.app` bundles
(`tmp.*/SimpleGui.app`) via `scripts/gui/macos-gui-run.shs` with
`examples/06_io/ui/widget_showcase_gui.spl` (evidence dir
`build/showcase-evidence/2026-09-17-reverify/`, 6 launcher runs).

**What improved — the title symptom is fixed.** While the app is alive,
System Events sees the process:

```
$ osascript -e 'tell application "System Events" to (name of processes whose name is "SimpleGui")'
SimpleGui
```

The 2026-05 predecessor's core tell ("NO matching process visible to System
Events") no longer reproduces — the process registers with the window
server/AX layer. Consistent with the source fix now present at
`winit_sffi_thread.rs:407-409`
(`with_activation_policy(ActivationPolicy::Regular).with_activate_ignoring_other_apps(true)`)
plus the pre-window pump loop (:431-440).

**What remains open — no on-screen window appears.** Across two live checks
of running SimpleGui processes (runs 5 and 6, both alive past their
timeout via the watchdog):

```
$ osascript -e 'tell application "System Events" to tell process "SimpleGui" to count windows'
0
```

`screencapture` at the same moment shows a clean desktop (no SimpleGui
window). Both runs' logs end at
`rendered 343200 px from the shared showcase widget tree` with
`showcase_frame_backend=software;source=cpu_mirror` — i.e. the frame was
produced through the cpu_mirror path, the same "headless PPM snapshot, not a
real on-screen window" shape the 2026-05 record warned about. The drag and
click-counter acceptance steps therefore could not be exercised.

**Complicating facts for the next session** (each already has its own
record): the in-tree showcase entry needed a compile workaround
(`showcase_resolution_wh` undefined — see
`toolchain_gaps_exposed_by_wm_web2d_retained_perf_gate_2026-09-17.md` Gap 2;
the runs used a working copy), and the pure-Simple darwin binary that could
settle the native-path question is defective on its own source snapshot
(`pure_simple_darwin_macho_binary_build_defective_2026-09-17.md`).

**Verdict: partially resolved, kept OPEN.** Window-server/AX registration
works; an actually-visible, interactive window is still unproven on this
host. Re-verify once a source-matched pure-Simple darwin binary with the gui
feature runs end-to-end.

## Symptom

The widget-showcase window launched via `scripts/gui/macos-gui-run.shs` **renders and composites
on screen** (visible, correct pixels — evidence `build/showcase-evidence/standalone_screen.png`;
`CGWindowListCopyWindowInfo` lists the surface `onscreen=true, layer=0`), but the owning process
has **no application-level activation/accessibility registration** — the compositor knows the
surface, the Aqua session does not know the app:

1. **User-confirmed:** the window cannot be dragged and does not respond to any interaction
   (clicks never land — the window never becomes frontmost/key).
2. **Programmatic raise/position fails silently:** System Events sees no process named
   `"SimpleGui"` and no process by `unix id` even while `ps`/`pgrep` show it alive
   (`osascript` → "no process for pid …"). The launcher's own nudge loop
   (`scripts/gui/macos-gui-run.shs:93-111`, name-based `tell application "SimpleGui"`)
   silently no-ops on the same query, so the window is left behind other windows under load.
3. **Screen-recording/allowlist layer can't bind it:** computer-use
   `request_access(["SimpleGui"])` → denied `not_installed` (throwaway bundle id
   `com.simple.gui.run.$$` under `/var/folders`, never LaunchServices-installed).
4. **Consequence:** real OS input (CGEvent via `cliclick`) cannot be delivered to the app —
   the click lands on whatever window IS frontmost. Titlebar drag does not move the window
   (see drag-regression evidence below).

## Repro

```sh
# from repo root, macOS (needs src/compiler_rust/target/gui/debug/simple built with --features gui)
SIMPLE_TIMEOUT_SECONDS=200 scripts/gui/macos-gui-run.shs examples/06_io/ui/widget_showcase_gui.spl
# window appears (composited) after ~20-40 s (debug driver, interpret mode), then:
osascript -e 'tell application "System Events" to count windows of (processes whose name is "SimpleGui")'
#   -> error / empty: process invisible to accessibility layer
cliclick dd:460,130 w:300 dm:530,170 dm:610,210 w:200 du:610,210   # titlebar drag
# -> window does not move; clicks/typing never land in the app
```

## Evidence (build/showcase-evidence/)

- `standalone_screen.png` — window composited on-screen, full widget gallery (render itself OK).
- `click_before.png`, `standalone_before_click.png`, `standalone_after_click.png` — injection
  attempts: window not frontmost / not raisable, CGEvent clicks land elsewhere.
- `drag_before.png` / `drag_after.png` + `drag_test.txt` + `drag_after_windowlist.txt` —
  explicit titlebar-drag regression test (EXECUTED, FAIL as expected today):
  window-server bounds `X=200 Y=120 520x692` before AND after a real CGEvent titlebar drag
  of (+150,+80) — **delta (0,0)**; the mouse-down was instead routed to the occluded window
  behind (menu bar flipped SimpleGui → Terminal). `CGWindowListCopyWindowInfo` DOES see the
  window (`onscreen=true, layer=0`) — the surface is composited; what's missing is the
  process-level activation/AX registration, so no input routing. This pair is the
  regression check for the #25 fix: after the fix the window must move by the drag delta
  and keep frontmost.
- `standalone_launch_cmd*.out` — launcher outputs incl. silent nudge no-op.
- Launcher nudge code: `scripts/gui/macos-gui-run.shs:93-111`.

## Root-cause direction

The CLI-spawned GUI driver never sets an **NSApplication activation policy** — a plain
`NSApplicationActivationPolicyProhibited`-equivalent process owns the window, so the Aqua
session composites the surface but does not register it as an interactive application:
no Dock/app-switcher entry, no accessibility (AX) tree, cannot become frontmost/key, no
mouse/keyboard routing. The `.app`-bundle wrapper (macos-gui-run.shs) was enough to make
the window *display* (2026-05-28 bug) but not to register it for *interaction*.

**Fix (owned by GuiRenderer/spl_winit, task #25):**
- Set activation policy **Regular** (`NSApp.setActivationPolicy(.regular)`) in the winit
  runtime before the first window is mapped, and call
  `NSApp.activate(ignoringOtherApps:)` after map.
- Then the launcher nudge can be made deterministic (and should target the launched PID,
  not the process name, since examples-safety re-execs an isolated child).

## Regression test (for #25)

Re-run the drag repro above; PASS criteria:
1. `System Events` finds the process and `count of windows` >= 1;
2. titlebar CGEvent drag moves the window by the drag delta (compare
   `drag_before.png`/`drag_after.png` window bounding boxes);
3. a CGEvent click on the "Run" button increments the on-frame `Clicks` counter
   (`SIMPLE_EVT_LOG` shows `[widget-showcase] input left_button …`).
