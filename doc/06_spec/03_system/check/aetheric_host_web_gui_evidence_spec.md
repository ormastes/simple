# Aetheric host Web/GUI evidence

Status: **production producer added; PASS blocked on canonical Electron
ui_access adapter and an exact-current self-hosted binary.**

The only PASS input is a regular-file `aetheric-host-web-gui-v1` bundle from
the production HTML/WebIR-to-DrawIR Electron route. It must retain resolved
`aetheric_dark` snapshot hashes, computed glass CSS, Engine2D pixels, canonical
snapshot/surface/find/act/history receipts, focus/pointer/key/text state,
animation/performance facts, and capture/binary/source provenance.

Run after the exact-current binary is available:

```sh
SIMPLE_BIN=/absolute/path/to/simple \
AETHERIC_HOST_WEB_GUI_PROOF=build/aetheric-host-web-gui-evidence/aetheric-host-web-gui.env \
sh scripts/check/check-aetheric-host-web-gui-evidence.shs
```

Missing proof, fixture, raw-source, compatibility-renderer, blur, or tolerance
claims are failures, never skips or PASS.

The producer first resolves `aetheric_dark` through the production Simple
package loader, generates the current WM HTML, renders that HTML through
WebIR/DrawIR/Engine2D, and then captures the same file with Electron. Electron
records computed CSS, animation frames, native pointer/key/text events, and a
PNG. The canonical `ui_access` service does not yet register this standalone
capture surface, so the proof deliberately remains `status=fail` with the
tracked `electron-capture-surface-not-registered-with-canonical-ui-access` ABI
gap rather than fabricating snapshot/action/history receipts.

Before a proof can pass, the admission wrapper recomputes the current source
revision, self-hosted binary SHA-256, and all three artifact SHA-256 values;
all artifacts must be regular files beneath `BUILD_DIR`.
