# Aetheric host Web/GUI evidence

Status: **production producer and canonical Electron UI-access adapter are
implemented; live PASS is pending an exact-current native renderer build.**

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
PNG. A narrow native driver invokes the canonical `run_ui_access_cli`; the
Electron process serves its exact live DOM through the canonical
snapshot/surface/find/act/history protocol. Every action is revision-bound and
the proof retains both the request/result history and the post-action DOM
state. The admission wrapper requires the CSS animation probe to be `true`, in
addition to positive `performance.now()` and at least two animation frames.

Before a proof can pass, the admission wrapper recomputes the current source
revision, self-hosted binary SHA-256, and all three artifact SHA-256 values;
all artifacts must be regular files beneath `BUILD_DIR`. The latest live
producer attempt stops fail-closed while linking the native Simple renderer.
Three compiler fix/review cycles were rejected on custom-method, inferred-text,
and cross-backend float semantics; the candidate was not integrated and the
remaining producer cycle was not spent. No Electron capture or PASS is
admitted from the partial run.
