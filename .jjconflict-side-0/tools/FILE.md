# tools/ Manifest

Declares allowed entries under `tools/` (developer tooling, not part of the
compiler or stdlib). Enforced by `scripts/check-workspace-root-guard.shs`.

## Allowed Entries

| Entry | Description |
|---|---|
| `chrome-live-bitmap` | Chrome-based live bitmap capture harness |
| `claude-plugin` | Claude Code plugins (codex-research, dev, gemini-ui-design, sstack, verify-agent, marketplace + cmm-lsp/obsidian-search manifests) |
| `docker` | Dockerfiles for cross-language perf and test-isolation containers |
| `electron-live-bitmap` | Electron-based live bitmap capture harness |
| `electron-shell` | Electron desktop shell |
| `electron-wasm-gui-exec` | Electron WASM GUI execution harness |
| `gui_perf_bench` | Cross-toolkit GUI perf benchmark harness (GTK/JS/Python) |
| `jupyter` | Jupyter integration |
| `lsp-mcp-registry` | LSP MCP server registry metadata |
| `mcp-registry` | MCP server registry metadata |
| `node-render-bitmap` | Node.js render-to-bitmap harness |
| `pixel_compare` | Pixel comparison tool |
| `ref_crypto` | Reference crypto implementations |
| `tauri-live-bitmap` | Tauri live-bitmap capture harness (WKWebView snapshot backend) |
| `tauri-shell` | Tauri 2 mobile/desktop shell (iOS + Android + desktop) — see `doc/07_guide/platform/mobile/tauri_mobile_guide.md` |
| `web-render-backend` | Web rendering backend harness |
| `FILE.md` | This manifest |
