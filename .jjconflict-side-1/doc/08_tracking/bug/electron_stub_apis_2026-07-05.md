---
id: electron_stub_apis_2026-07-05
status: RESOLVED
severity: high
discovered: 2026-07-05
discovered_by: Code review of src/app/ui.electron/main.spl and src/app/ui.electron/bridge.js
resolved: 2026-07-05
related: src/app/ui.electron/main.spl
related: src/app/ui.electron/bridge.js
related: src/app/ui.ipc/protocol.spl
related: tools/electron-shell/{package.json,main.js,preload.js}
---

# Electron backend: stub APIs and missing multi-window (MDI) support

## Summary (as filed)

Two gaps were filed against the Electron backend:

1. `notify()`/`open_file_dialog()` in `main.spl` (lines 135-149) were
   TODO(v4-dev-preview) stubs that printed and returned a hardcoded value.
2. `bridge.js` line 943 and surrounding `BrowserWindow` management were
   read as single-window-only, with no internal-window (MDI) surface
   routing.

## Findings on investigation (2026-07-05)

Gap 2 was already resolved in the tree by the time this bug was
investigated: `bridge.js` (`electronWmInitScript`/`receiveElectronMessage`)
already renders internal windows as positioned `.wm-window`/`.wm-titlebar`
DOM elements inside the single top-level `BrowserWindow`, reusing the same
`wm-desktop` class contract `window_scene_draw_ir.spl` and the web lane use
for `gui/core`. What *was* broken and blocking any verification of this: the
gate's `tools/electron-shell/{package.json,main.js,preload.js}` scaffolding
had been deleted (commit `c8dbb4df4f`), so `check-electron-mdi-evidence.shs`
could not even launch Electron. Restored those three files (unchanged
content — thin wrappers into `src/app/ui.electron/{bridge.js,preload.js}`).
With them restored, a manual run of the gate's underlying Electron
invocation (`SIMPLE_BIN` pointed at the macOS build) produced a genuine
4-window screenshot + JSON proof: `count:4`, `dragMoved:true`,
`bodyClickRouted`/`bodyInputRouted`/`bodyKeyRouted:true`,
`trafficMinimizeRouted`/`trafficMaximizeRouted`/`trafficCloseRouted:true`,
6-item taskbar visible — validated `pass` by both
`scripts/check/validate-electron-mdi-proof.js` and the two
`ios_mdi_probe_server.spl --validate-*-screenshot` checks the gate script
also runs.

Gap 1 was half-real: `notify()` already built the correct
`{"type":"notification",...}` message and `bridge.js` already had a real
`new Notification(...).show()` handler for it — functionally wired, just
mislabeled as a stub in comments (fixed the comment). `open_file_dialog()`
was genuinely broken: it built a `{"type":"fileDialog",...}` message that
`bridge.js` had **no handler for at all** (silently dropped), then
unconditionally returned `true`. Fixed by adding a `fileDialog` handler in
`bridge.js` (`runFileDialog`) that calls the real
`dialog.showOpenDialog`/`showSaveDialog`, and round-trips the real result
back over stdin as a `fileDialogResult` message (parsed in
`app.ui.ipc.protocol.parse_ipc_message` into
`UIEvent.Action(name: "file_dialog_result:" + paths)`, reusing the existing
Action-encoding convention rather than adding a new `UIEvent` variant to
every exhaustive event-pipeline match). `open_file_dialog()`'s signature
changed from `-> bool` to `-> text`, blocking on stdin for the real
selection (or `""` on cancel) — no other caller depended on the old
signature.

## Verification evidence

- Live Electron run (macOS, real `BrowserWindow`, no mocks) produced
  `build/electron_mdi_manual/{proof.json,shot.png}`; both proof-validator
  scripts the CI gate uses passed cleanly.
- `bin/simple test test/01_unit/app/ui/ipc_protocol_spec.spl` — 22/22
  passed, including two new cases parsing `fileDialogResult` (selected path
  and canceled) into the expected `UIEvent.Action`.
- Direct JS-level integration test (electron.dialog monkeypatched, real
  `handleSimpleMessageLine` invoked): confirms `dialog.showOpenDialog` is
  called with `{"properties":["openFile"],"filters":[{"name":"Files",
  "extensions":["spl","txt"]}]}` for `filters:"spl,txt"`, and
  `dialog.showSaveDialog` for `dialogType:"save"` — i.e. the real API is
  genuinely invoked, not faked.

## Remaining gaps (not fixed here, stated plainly)

- `check-electron-mdi-evidence.shs` itself only runs under Linux+Xvfb
  (`command -v xvfb-run` is a hard requirement) and its `SIMPLE_BIN`
  auto-detect glob (`release/*/simple` before `bin/release/*/simple`) prefers
  a Linux binary even on macOS — it must be invoked with `SIMPLE_BIN` set
  explicitly there. Not changed in this pass since the script is
  intentionally Linux-CI-shaped; flagged here rather than silently patched.
- This backend remains dev-preview-only and is not wired into CI.
- `ElectronMain` (`main.spl`) is not the process `bridge.js`'s
  `startSimpleProcess` actually spawns today (that's `app.spl`'s
  `run_electron`); it is exercised via `ElectronMain.new`/`.start()` in
  `test/01_unit/app/ui.electron/main_spec.spl` and via `wm_compare`-style
  compositor snapshotting, not via a live spawned subprocess. The stdout/
  stdin protocol fix is correct either way since it's the same wire format
  `app.spl`/`ElectronBackend` already use, but no test spawns `ElectronMain`
  end-to-end through a real `bridge.js` process.

## Related

- Target architecture: doc/04_architecture/ui/mdsoc_architecture_tobe.md (MDSOC+ section)
- Completed backends: Tauri (Android live, iOS sim-only), winit WM (macOS Metal + HTML web)
