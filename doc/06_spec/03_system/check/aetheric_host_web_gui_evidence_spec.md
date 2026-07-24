# Aetheric host Web/GUI evidence

Status: **live evidence pending an exact-current self-hosted binary.**

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
