# Window Manager UI Export Plan

## Goal

Make the window manager UI render from a single HTML/CSS representation for visual iteration, then export that same snapshot for Stitch analysis.

## Current State

- Electron shell already renders the UI and can dump the rendered HTML payload to disk via `SIMPLE_UI_DUMP_HTML_PATH`.
- `scripts/export_ui_snapshot.shs` exists as the local snapshot entrypoint.
- `stitch-mcp` is installed and registered in Codex.
- A valid local env file exists at `~/.security/env.sh`.

## Blockers

- The current Codex session has not been restarted, so Stitch MCP is not exposed as a callable tool in this chat.
- Direct Stitch upload cannot happen until the restarted session can see the connector.

## Next Steps

1. Restart the Codex session so the MCP registry reloads.
2. Re-run the export flow against the desired UI entry.
3. Hand the resulting HTML snapshot to Stitch for analysis.
4. Apply the next UI polish pass from the capture, then repeat.

## Artifact Paths

- Electron HTML export hook: `tools/electron-shell/main.js`
- Snapshot script: `scripts/export_ui_snapshot.shs`
- Example snapshot output: `build/ui_snapshots/demo_menubar_statusbar.electron.snapshot.html`
- Example PNG preview: `build/ui_snapshots/demo_menubar_statusbar.electron.snapshot.png`

