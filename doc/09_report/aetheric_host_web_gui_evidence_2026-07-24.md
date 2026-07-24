# Aetheric host Web/GUI evidence — 2026-07-24

Status: **contract ready; live evidence pending exact-current Simple.**

The new admission wrapper accepts only a regular-file proof from the production
`HTML/WebIR -> DrawIR -> Engine2D -> Electron` route. It rejects missing
artifacts and every shortcut flag, then verifies the Aetheric snapshot hashes,
glass computed-style facts, nonblank capture, canonical UI-access history and
post-action state, animation/performance values, and binary/source provenance.

No live run was attempted because this isolated worktree has no self-hosted
`bin/simple`; a synthetic bundle is intentionally insufficient to PASS.

Resume after the exact-current binary and real producer bundle exist:

```sh
SIMPLE_BIN=/absolute/path/to/simple \
AETHERIC_HOST_WEB_GUI_PROOF=build/aetheric-host-web-gui-evidence/aetheric-host-web-gui.env \
BUILD_DIR=build/aetheric-host-web-gui-evidence \
sh scripts/check/check-aetheric-host-web-gui-evidence.shs
```
