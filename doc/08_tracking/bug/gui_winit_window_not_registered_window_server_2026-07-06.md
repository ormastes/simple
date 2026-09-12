# BUG: winit GUI window composites but is not registered with the macOS window server / accessibility layer

- **Date:** 2026-07-06
- **Severity:** HIGH — blocks ALL live GUI interaction on macOS (clicks, typing, drag, programmatic control)
- **Status:** open
- **Area:** GUI / winit runtime / macOS launch path
- **Fix owner:** GuiRenderer / spl_winit work (task #25)
- **Related:** `doc/08_tracking/bug/macos_winit_window_not_displayed_2026-05-28.md` (predecessor: window not displayed at all; this bug is the residue after the .app-bundle workaround makes it display)

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

## 2026-09-12 (Lane 4) — still OPEN, but the recorded root-cause direction is now partly stale

Read-only re-check on Apple M4 at `origin/main` = `b9667d6584f`. Not patched:
the remaining work is in the Rust winit runtime, outside this lane's file scope.

Two of the three things the "Root-cause direction" section proposes are already
done, so a future session must not re-do them:

- **Activation policy Regular is ALREADY set.**
  `src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_thread.rs:408`
  builds the event loop `.with_activation_policy(ActivationPolicy::Regular)`
  (import at `:19`). The claim that "a plain
  NSApplicationActivationPolicyProhibited-equivalent process owns the window" is
  therefore no longer accurate as written. Whether it takes effect for a process
  launched through the throwaway `.app` is unverified.
- **The generated bundle plist is clean.** `scripts/gui/macos-gui-run.shs`
  writes no `LSUIElement` and no `LSBackgroundOnly` key
  (grep: zero hits), so the bundle is not asking to be a background app.

What is still missing, and is the exact remaining edit:

1. `NSApp.activate(ignoringOtherApps:)` after the first window is mapped —
   `with_activation_policy` alone sets the policy but does not make the app
   frontmost/key, which is what the drag and click repros need.
2. LaunchServices registration. The bundle id is `com.simple.gui.run.$$` under
   `/var/folders` and is never `lsregister`-ed, which is why computer-use
   `request_access(["SimpleGui"])` answers `not_installed`. Deliberately NOT
   added here: registering throwaway per-PID bundle ids pollutes the
   LaunchServices database, so the fix belongs with a stable bundle id, not with
   an `lsregister -f` call on a `$$`-suffixed bundle.

The regression test in this record (drag delta, System Events window count,
Clicks counter) is unchanged and remains the acceptance bar. It was not run this
session: with the activation edit not made, a run could only re-confirm the
recorded FAIL, and the session's GUI budget went to the launcher defects fixed in
`doc/08_tracking/bug/macos_gui_run_sigpipe_141_and_stale_winit_marker_gate_2026-09-06.md`
(RESOLVED), which had to land first — until this week the launcher exited 141
after every successful launch, so the drag repro could not even report its own
exit status honestly.
