---
id: ui_browser_main_open_fake_planner_2026-07-05
status: OPEN
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

## Fix direction (not applied here — see companion perf bug before wiring)

Make `--open` real: import `run_browser_gui` from `app.ui.browser.app` and
call it when `open_flag` is set, mirroring `cli_browser`. Keep the current
plan-printing behavior behind a new `--plan`/`--dry-run` flag (or as the
default when `--open` is absent) so source-mode readiness probing still
works without a display. **Do not wire this until**
`doc/08_tracking/bug/browser_engine_css_size_quadratic_pixel_render_2026-07-04.md`
(and its 2026-07-05 cross-validation addendum below) is resolved — with that
bug still open, actually calling `run_browser_gui` from `--open` trades a
silent no-op for an indefinite hang, which is a worse user experience. This
session added stage-by-stage progress logging
(`src/app/ui.browser/app.spl`, `src/app/ui.browser/backend.spl`) so that once
`--open` is wired, a hang becomes diagnosable on stderr instead of silent
either way.

## Verification

Confirmed via direct reproduction above (exit 0, plan-only output, no window,
no import of `run_browser_gui`/`BrowserApp` anywhere in the file).
