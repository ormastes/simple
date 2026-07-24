# Aetheric host Web/GUI evidence — 2026-07-24

Status: **production producer ready; PASS blocked by a precise Electron
canonical-ui-access ABI gap and exact-current Simple availability.**

The new admission wrapper accepts only a regular-file proof from the production
`HTML/WebIR -> DrawIR -> Engine2D -> Electron` route. It rejects missing
artifacts and every shortcut flag, then verifies the Aetheric snapshot hashes,
glass computed-style facts, nonblank capture, canonical UI-access history and
post-action state, animation/performance values, and binary/source provenance.

`scripts/check/produce-aetheric-host-web-gui-evidence.shs` now runs the current
self-hosted binary to resolve the `aetheric_dark` package and generate the WM
HTML, renders that exact file through WebIR/DrawIR/Engine2D, then captures it
with Electron. The Electron capture records the required computed CSS,
animation frames, real pointer/key/text events, ARGB pixels, and screenshot.
The proof writer joins only those on-disk facts.

The producer is intentionally fail-closed: the canonical `ui_access` service
can persist a `UISession` for the Electron app backend, but it cannot register
the standalone Electron capture `BrowserWindow` used for this exact generated
surface. It writes `electron-capture-surface-not-registered-with-canonical-ui-access`
and leaves every snapshot/surface/find/act/history status blocked. No DOM state
is translated into a private lookalike UI-access model.

The admission wrapper now recomputes the exact current revision, binary SHA,
and capture/pixel/screenshot SHA values, requires the artifact files beneath
`BUILD_DIR`, and rejects altered provenance. No live run was attempted because
this isolated worktree has no self-hosted `bin/simple`; a synthetic bundle is
intentionally insufficient to PASS.

Resume after the exact-current binary and real producer bundle exist:

```sh
SIMPLE_BIN=/absolute/path/to/exact-current-simple \
BUILD_DIR=build/aetheric-host-web-gui-evidence \
sh scripts/check/produce-aetheric-host-web-gui-evidence.shs && \
SIMPLE_BIN=/absolute/path/to/exact-current-simple \
BUILD_DIR=build/aetheric-host-web-gui-evidence \
sh scripts/check/check-aetheric-host-web-gui-evidence.shs
```
