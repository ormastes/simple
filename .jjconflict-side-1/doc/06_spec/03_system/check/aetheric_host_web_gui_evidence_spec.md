# Aetheric host Web/GUI evidence

Status: **production producer and canonical Electron UI-access adapter are
implemented; live PASS is pending an exact-current native renderer build.**

The only PASS input is a regular-file `aetheric-host-web-gui-v1` bundle from
the production HTML/WebIR-to-DrawIR Electron route. It must retain resolved
`aetheric_dark` snapshot hashes, computed glass CSS, Engine2D pixels, canonical
snapshot/surface/find/act/history receipts, focus/pointer/key/text state,
animation/performance facts, and capture/binary/source provenance.
It also binds the launched Electron runtime to exact version `42.5.0`: the
capture records Electron and Chrome process versions, while the proof retains
canonical launcher, application executable, installed package, and lockfile
paths with SHA-256 hashes that admission independently revalidates.
Those paths must resolve to the physical repo-local
`node_modules/electron/cli.js`, macOS application executable, installed
`package.json`, and source `package-lock.json`; another canonical file with a
matching substituted hash is rejected. Admission also parses the source
manifest dependency, lock root dependency, lock installed-package row, and
installed package version, all of which must equal `42.5.0`.

Both the producer and checker require an explicit current-source Stage4
`SIMPLE_BIN` and the mandatory adjacent `${SIMPLE_BIN}.provenance.env`. They
source `scripts/check/lib/bootstrap-stage3-provenance.shs` and
`scripts/check/lib/stage4-candidate-provenance.shs`, canonicalize the binary,
and call `stage4_verify_candidate_provenance` before producing or admitting
evidence. Missing, unreceipted, stale, source-mismatched, or hash-mismatched
binaries fail nonzero; there is no release, Stage3, repository, or `PATH`
fallback.

Run after the exact-current binary is available:

```sh
SIMPLE_BIN=/absolute/path/to/current-stage4/simple \
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

The generator, renderer, and UI-access driver use separate native caches. The
renderer link is explicitly bound to the validated WM and C-WM runtime
providers. The UI-access driver is explicitly bound to a freshly compiled
`runtime_sqlite.o` and the macOS SDK SQLite text stub because canonical UI
history persistence owns the SQLite dependency. A hashed, atomic provider
manifest records the exact compiler, source, provider, cache, and output
bindings. The proof writer carries that manifest and each provider path/hash;
admission independently checks canonical regular-file paths, hashes, current
SQLite source, native binary bindings, and cache separation.
