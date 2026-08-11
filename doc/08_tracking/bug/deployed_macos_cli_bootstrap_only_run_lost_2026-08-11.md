# Deployed macOS arm64 CLI is bootstrap-only: run/test/check/query lost on redeploy (2026-08-10)

- **Date:** 2026-08-11
- **Severity:** critical for local tooling (MCP/LSP restart breakage, all GUI/check gates that need `run`)
- **Area:** bin/release/aarch64-apple-darwin-macho/simple deployment; redeploy gate coverage

## Symptom
`bin/release/aarch64-apple-darwin-macho/simple` (132 MB, deployed 2026-08-10
09:00, receipt `simple.arm64-compiler-receipt.env`, schema
`simpleos-arm64-compiler-receipt-v1`) identifies as `simple-bootstrap 1.0.0-beta`
and supports only `compile`/`native-build`:

```
$ bin/simple run <file.spl>        → error: unknown command 'run'
$ bin/simple test|check|query …    → error: unknown command '…'
```

`bin/simple` (untracked local wrapper) execs this binary, so every `run`-based
flow is broken for any process started after the redeploy. The currently alive
MCP/LSP processes still work only because they hold the pre-redeploy inode
(started 2026-08-04). A restart of
`…/simple run src/app/simple_lsp_mcp/main.spl` (as .mcp.json does) fails today.

The bootstrap script's own redeploy gate
(`scripts/check/cert/redeploy_gate/redeploy_gate.shs`, fixture
`fixtures/p2_add.spl` executed via `run`) exists precisely to prevent this —
the bootstrap_main artifact should not have landed at the full-CLI path.

## Impact observed this session
- electron/tauri shells spawn `<simple-bin> run …` → instant failure.
- `check-production-gui-web-backend-executed-evidence.shs` and the GUI parity
  orchestrator: no admissible binary (seed is refused fail-closed).
- `bin/release/macos-arm64/simple` (older full CLI, Apr 11) errors
  `Error running <file>` for every input — also not usable.

## Fix direction
1. Rebuild + deploy the full CLI from `src/app/cli/main.spl`
   (`bootstrap-from-scratch.sh --mode=dynload --full-cli --deploy`) — currently
   blocked by stage4_surface_fingerprint_mismatch_log_modes_2026-08-11.md.
2. Keep the simpleos arm64 *compiler* artifact at a distinct filename (e.g.
   `simple_bootstrap_compiler`) so the compiler receipt lane cannot clobber the
   CLI path.
3. Extend the redeploy gate with a `run` smoke on the DEPLOYED path post-copy
   (today the gate checks the candidate pre-deploy only).
