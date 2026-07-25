---
id: ui_browser_main_open_fake_planner_2026-07-05
status: FIXED
severity: high
discovered: 2026-07-05
discovered_by: Browser GUI launch investigation (user report: browser hangs/silently fails to launch)
related: src/app/ui.browser/main.spl
related: src/app/cli/browser.spl
related: src/app/ui.browser/app.spl
---

# `src/app/ui.browser/main.spl --open` never launches anything — it only prints a plan

## Summary

`src/app/ui.browser/main.spl` is the entry point a user reaches by running
`bin/simple src/app/ui.browser/main.spl <file.ui.sdn> --open` (the natural
thing to try since the deployed `bin/simple` binary is missing the `browser`
subcommand — see `src/app/cli/browser.spl`'s header comment, a separate,
already-known, already-being-fixed issue). Its own header literally says:

```
# Startup-light command planner for source-mode help and readiness probes.
```

and the `--open` flag's help text says `Plan interactive browser startup`.

This is not a documentation quirk — it is accurate. `main()` in this file
never imports or calls `run_browser_gui` / `BrowserApp` at all. Regardless of
`--open`, it computes a `file_path`/`snapshot_path`/`backend`/`open_flag`/
`shared_wm` tuple and only `print`s it (or emits JSON), then returns 0.
`shared_wm_requested_browser()` and `shared_wm_backend_kind_browser()` are
defined but never called from `main()` either — the `--shared-wm` plan is
equally inert.

## Reproduction

```bash
$ SIMPLE_EXECUTION_MODE=interpret bin/simple src/app/ui.browser/main.spl \
    examples/06_io/ui/widget_showcase_mobile.ui.sdn --open
ui.browser-plan: 1/1 (100%)
UI browser file: examples/06_io/ui/widget_showcase_mobile.ui.sdn
Snapshot: .build/ui_browser/snapshot.ppm
Backend: auto
Open: true
Shared WM: false
$ echo $?
0
```

No window is created, no error is printed, exit code is 0. From a user's
perspective this looks exactly like "the browser silently failed to start" —
worse, the "Open: true" line actively suggests it worked.

## Root cause

`main()` (lines 13–72) is a pure CLI-arg-to-plan-text formatter. Compare with
`src/app/cli/browser.spl:cli_browser()`, which is the *real* dispatcher (used
by the in-process `bin/simple browser` subcommand once that binary is
redeployed): it correctly does

```simple
if open_flag:
    return run_browser_gui(file_path, 0)
```

`src/app/ui.browser/main.spl` has no equivalent call anywhere.

## Fix applied

`src/app/ui.browser/main.spl` now imports
`run_browser_gui_with_access_store` from `app.ui.browser.app` and, when
`--open` is passed (and `--dry-run`/`--plan` is not), calls it directly —
mirroring `cli_browser`. The old unconditional plan-printing is preserved as
the default (no `--open`) and can also be forced with the new `--dry-run` /
`--plan` flag even when `--open` is present, so source-mode readiness
probing without a display still works.

This was wired despite
`doc/08_tracking/bug/browser_engine_css_size_quadratic_pixel_render_2026-07-04.md`
(cross-validation addendum below) still being open — i.e. a real `--open`
launch can currently take a very long time (observed >5 minutes, not
confirmed to terminate) to present its first frame. That tradeoff was made
deliberately: this session added stage-by-stage progress logging
(`src/app/ui.browser/app.spl`, `src/app/ui.browser/backend.spl`, on stderr by
default, respects `--quiet`) so a slow/stuck launch is now diagnosable
(exact stage reached, e.g. `window-created` then stuck before
`pixel-artifact-done`) instead of the previous silent "it worked" plan text.
An honest hang-with-diagnostics is a strictly better user experience than a
silent fake success.

## Verification

- Before fix: `bin/simple src/app/ui.browser/main.spl <file> --open` → exit
  0, prints `Open: true` and a plan, no window, no error, no import of
  `run_browser_gui`/`BrowserApp` anywhere in the file.
- After fix:
  - `--open --dry-run` / no `--open` → unchanged plan-printing behavior
    (verified both still print the plan and exit 0).
  - `--open` (no dry-run), run via the non-GUI `bin/simple` binary → now
    genuinely attempts the launch and fails with
    `error: semantic: unknown extern function: rt_winit_event_loop_new`
    (the winit runtime is only linked into the GUI-enabled driver — see
    `scripts/gui/macos-gui-run.shs`), with stage logs on stderr showing
    exactly how far it got:
    ```
    [browser] args-parsed: file=... backend=auto
    [browser] backend-resolve-start: requested=auto w=96 h=64
    [browser] backend-selected: software
    [browser] app-init-done
    [browser] window-create-start: w=672 h=448
    error: semantic: unknown extern function: rt_winit_event_loop_new
    ```
  - `--open` run via the GUI-enabled driver + `scripts/gui/macos-gui-run.shs`
    reaches `window-created` (the real winit window is created) and then
    stalls inside `render_frame()` per the companion perf bug doc.
