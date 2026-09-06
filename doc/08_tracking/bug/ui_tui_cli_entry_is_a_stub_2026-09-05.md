# `simple ui tui` runs a stub; the real TUI app is unreachable from the CLI

**Date:** 2026-09-05 · **Status:** OPEN · **Lane:** ui_slim_kernel_plugin (found while gating the product entry)

## Evidence

- `src/app/cli/command_registry.spl:68` → `src/app/ui/main.spl:10` and
  `src/app/ui/backend_entry_tui.spl:2` both import `app.ui.tui.app.{run_tui}`.
- `src/app/ui.tui/app.spl:22` `run_tui(file_path)`: checks the file exists, enters the
  alternate screen, prints the literal `Simple UI`, blocks on one line of input, leaves the
  alternate screen. It never parses or renders the `.ui.sdn` file. Its own header says
  "this module is the hot native terminal entrypoint used by startup-size audits".
- The parser-backed TUI (`src/app/ui.tui/async_app.spl`, `run_async_tui`) has NO CLI caller:
  its only reference is the `src/app/ui.tui/__init__.spl:15` export (verified 2026-09-05).

## Why it matters

Every historical "TUI startup" number for `simple ui tui` measured a stub, and any
"opening speed" work on `async_app.spl` (today's 343 → 9 file closure reduction) does not
reach the shipped command until it is wired. The design's T1 workload (80×24, visible
greeting, input-ready, deterministic quit) needs a real entry.

## Unblock (decision needed)

Either wire `run_tui` to `run_async_tui`/`run_tui_routed` (`shared_wm_route.spl`) now that
the ordinary route no longer drags the compositor in, keeping the stub only behind an
explicit `--stub` for size audits; or declare `tui_web` the product TUI and delete the
dead route. Pick one, then re-gate with `scripts/check/check-ui-slim-closure.shs` on the
terminal module and measure T1.
