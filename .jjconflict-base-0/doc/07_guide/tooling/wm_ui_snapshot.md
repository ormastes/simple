# Window Manager HTML/CSS Snapshot Guide

Version: 1.0.0
Date: 2026-04-08
Status: Active

## Goal

Export the window-manager UI through the shared HTML/CSS rendering path, then generate screenshot artifacts for visual review and Stitch import.

This flow is useful when:

- the WM or desktop chrome needs a visual polish pass
- a UI capture is needed for Stitch or another design tool
- the exported HTML must stay close to the renderer used by Simple UI

## What Gets Exported

There are two related outputs:

- `*.electron.snapshot.html`: a self-contained HTML snapshot
- `*.png`: a rendered screenshot of that snapshot

The HTML snapshot is the source of truth for the exported UI state. The PNG is the transport artifact for visual tools such as Stitch.

## Rendering Path

The export tooling tries the live Electron render path first.

Primary path:

- `bin/simple run src/app/ui.electron/app.spl <entry.ui.sdn>`
- Electron receives the first `render` IPC payload
- `tools/electron-shell/export_snapshot.js` writes that HTML to the requested output path

Fallback path:

- `tools/electron-shell/export_snapshot.js` falls back to `tools/electron-shell/export_snapshot.spl`
- the fallback uses `app.ui.web.html.generate_html_page`
- this still stays on the shared HTML/CSS output path and produces a single-file document

Use `--no-fallback` when validating the strict Electron IPC path. In normal visual
work, fallback keeps the output on the shared HTML/CSS path if Electron IPC render
does not start cleanly.

## Relevant Files

- `scripts/export_ui_snapshot.shs`: shell entrypoint for HTML export plus optional PNG
- `tools/electron-shell/export_snapshot.js`: main snapshot driver
- `tools/electron-shell/export_snapshot.spl`: shared HTML generator fallback
- `tools/electron-shell/main.js`: Electron shell and `SIMPLE_UI_DUMP_HTML_PATH` hook
- `tools/electron-shell/screenshot.js`: headless Electron screenshot helper
- `doc/plan/wm_ui_export_plan.md`: short operational plan for the WM export loop

## Typical Inputs

For UI pipeline validation:

- `examples/ui/demo_menubar_statusbar.ui.sdn`
- `examples/ui/demo_kitchen_sink.ui.sdn`

For SimpleOS / WM-related work:

- `examples/simple_os/hosted/hosted_wm.spl`
- `examples/simple_os/arch/x86_64/wm_entry.spl`
- `examples/simple_os/arch/arm64/wm_entry.spl`

The `.ui.sdn` demos are the easiest targets for HTML snapshot export because they already go through the UI renderer directly.

## Recommended Command

Use the wrapper script first:

```bash
sh scripts/export_ui_snapshot.shs \
  examples/ui/demo_menubar_statusbar.ui.sdn \
  build/ui_snapshots/demo_menubar_statusbar.electron.snapshot.html \
  build/ui_snapshots/demo_menubar_statusbar.electron.snapshot.png
```

This script:

- resolves the Electron binary
- launches the Electron shell
- waits for `SIMPLE_UI_DUMP_HTML_PATH` to be written
- optionally runs `tools/electron-shell/screenshot.js`

## Direct Snapshot Command

Use the Node driver when more control is needed:

```bash
node tools/electron-shell/export_snapshot.js \
  --entry examples/ui/demo_menubar_statusbar.ui.sdn \
  --png build/ui_snapshots/demo_menubar_statusbar.electron.snapshot.png
```

Useful options:

- `--out <path>`: explicit HTML output path
- `--png <path>`: also render a PNG
- `--width <n>`: screenshot width
- `--height <n>`: screenshot height
- `--timeout-ms <n>`: wait time for first Electron render
- `--no-fallback`: fail instead of using the shared HTML fallback

## Direct HTML Dump Hook

The low-level hook lives in `tools/electron-shell/main.js`.

You can use it directly:

```bash
SIMPLE_UI_DUMP_HTML_PATH=build/ui_snapshots/demo.html \
  tools/electron-shell/node_modules/.bin/electron \
  tools/electron-shell \
  examples/ui/demo_menubar_statusbar.ui.sdn
```

This is useful when debugging the Electron shell itself rather than the wrapper tooling.

## Output Locations

Default HTML output from `export_snapshot.js`:

```text
build/ui_snapshots/<entry>.electron.snapshot.html
```

Example artifacts:

- `build/ui_snapshots/demo_menubar_statusbar.electron.snapshot.html`
- `build/ui_snapshots/demo_menubar_statusbar.browser.snapshot.png`
- `build/ui_snapshots/demo_kitchen_sink.electron.snapshot.html`
- `build/ui_snapshots/demo_kitchen_sink.browser.snapshot.png`

## Screenshot Generation Notes

The built-in screenshot helper is:

```bash
node tools/electron-shell/screenshot.js input.html output.png 1360 840
```

This uses headless Electron with `capturePage()`.

The snapshot driver wraps this helper with a timeout and process cleanup guard.
If the helper fails, keep the generated HTML and capture from a browser session;
the HTML is still the source-of-truth artifact.

## Stitch Usage

Current practical guidance:

- upload the PNG to Stitch
- keep the HTML snapshot beside it for fidelity checks and follow-up diffing

The PNG is the import artifact. The HTML is the exact exported representation of the current UI state.

Suggested Stitch prompt:

```text
Recreate this uploaded UI screenshot as an editable web design. Preserve the desktop app chrome, menubar/statusbar layout, spacing, hierarchy, and overall visual structure. Focus on fidelity over embellishment.
```

If multiple captures are needed, create separate Stitch generations rather than combining unrelated screens into one prompt.

## Troubleshooting

### Electron render never writes HTML

Check:

- the entry path exists
- `bin/simple` exists
- the shell can launch Electron

If the live Electron path fails, `export_snapshot.js` should fall back automatically unless `--no-fallback` is set.

### Export falls back immediately

This usually means the `bin/simple run src/app/ui.electron/app.spl <entry.ui.sdn>`
process exited before the first `render` message. The fallback HTML is still valid
for visual iteration.

### PNG generation fails

If `tools/electron-shell/screenshot.js` crashes or times out, keep the generated
HTML and produce the PNG with a normal browser session.

### Stitch MCP returns `401`

That is an authentication issue in the MCP process, not an HTML export issue. The HTML and PNG outputs are still valid and can be uploaded through an authenticated browser session.
