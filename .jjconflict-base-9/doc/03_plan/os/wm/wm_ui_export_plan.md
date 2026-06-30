# Window Manager UI Export Plan

## Goal

Make the window manager UI render from a single HTML/CSS representation for visual iteration, then export that same snapshot for Stitch analysis.

## Current State

- Electron shell already renders the UI and can dump the rendered HTML payload to disk via `SIMPLE_UI_DUMP_HTML_PATH`.
- `scripts/export_ui_snapshot.shs` exists as the local snapshot entrypoint.
- `stitch-mcp` is installed and registered in Codex, and Stitch is available again in the current workflow.
- A valid local env file exists at `~/.security/env.sh`.

## Status

- The earlier session-restart blocker is resolved.
- The remaining work is operational: export the target window-manager UI snapshot, feed it into Stitch analysis, and iterate on polish.

## Next Steps

1. Re-run the export flow against the desired UI entry.
2. Hand the resulting HTML snapshot to Stitch for analysis.
3. Apply the next UI polish pass from the capture.
4. Repeat export and Stitch review until the window-manager UI is visually stable.

## Artifact Paths

- Electron HTML export hook: `tools/electron-shell/main.js`
- Snapshot script: `scripts/export_ui_snapshot.shs`
- Example snapshot output: `build/ui_snapshots/demo_menubar_statusbar.electron.snapshot.html`
- Example PNG preview: `build/ui_snapshots/demo_menubar_statusbar.electron.snapshot.png`
