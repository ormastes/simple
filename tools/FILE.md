# tools/ Manifest

Declares allowed entries under `tools/` (developer tooling, not part of the
compiler or stdlib). Enforced by `scripts/check-workspace-root-guard.shs`.

## Allowed Entries

| Entry | Description |
|---|---|
| `chrome-live-bitmap` | Chrome-based live bitmap capture harness |
| `electron-live-bitmap` | Electron-based live bitmap capture harness |
| `electron-shell` | Electron desktop shell |
| `jupyter` | Jupyter integration |
| `node-render-bitmap` | Node.js render-to-bitmap harness |
| `pixel_compare` | Pixel comparison tool |
| `ref_crypto` | Reference crypto implementations |
| `tauri-shell` | Tauri 2 mobile/desktop shell (iOS + Android + desktop) — see `doc/07_guide/platform/mobile/tauri_mobile_guide.md` |
| `web-render-backend` | Web rendering backend harness |
| `FILE.md` | This manifest |
