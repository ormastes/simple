# NFR Requirements: Simple Web Engine Completion (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Approved by User (Option 1)
- **Target Branch:** `release/1.0.0` (never `main`)
- **Worktree:** `/Users/ormastes/work/web_2d_gui` (`work/web-engine-complete`)

## Selected NFR Targets: Release 1.0.0 Quality Gate

| ID | Metric / Constraint | Target | Verification Method |
|---|---|---|---|
| `NFR-WEB-001` | Pinned Engine2D JS bitmap regression | `mismatch_count = 0` across all pinned scenes | `JS_RENDER_RUNTIME=node sh scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs` |
| `NFR-WEB-002` | Chrome-159 layout & paint parity | Float stacking, grid `auto+flex`, inline `LayoutUnit` & button device-width specs pass `100%` | `bin/simple test --no-session-daemon` on focused `browser_engine` specs |
| `NFR-WEB-003` | Cross-engine glass/widget parity | `>= 80%` non-text agreement vs Chrome & Electron (`tol <= 8`) | `sh scripts/check/check-widget-shells-crossengine-evidence.shs` (or saved capture check) |
| `NFR-WEB-004` | Interactive browser responsiveness & JIT safety | `browser_window_wait` poll cycle `<= 16 ms`, resize coalesce `150 ms`, rendering stays in `main.spl` (zero silent tree-walk fallback) | Unit/integration spec on hit-test, scroll, history + `browser --open` smoke |
| `NFR-WEB-005` | Build, lint & cleanliness | `simple check` passes on modified `browser_engine`/`app/browser` modules; `0` `*_spec.spl` under `doc/06_spec`; all PRs merged to `release/1.0.0` | `simple check` + `gh pr merge --admin --merge` |
