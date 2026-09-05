# Aetheric host Web/GUI evidence — 2026-07-24

Status: **production producer and canonical UI-access adapter ready; PASS
blocked at the native Simple renderer link boundary.**

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

The standalone Electron process now exposes its exact live DOM over the
canonical snapshot/surface/find/act/history protocol, and a narrow native
driver invokes the production `run_ui_access_cli` owner. Actions bind the
canonical revision and retain request/result history plus post-action state;
no private lookalike UI model is used. The admission wrapper additionally
requires `css_animation_probe=true`, not merely the presence of that field.

The admission wrapper recomputes the exact current revision, binary SHA, and
capture/pixel/screenshot SHA values, requires the artifact files beneath
`BUILD_DIR`, and rejects altered provenance. The native producer generated the
current Aetheric document successfully. Two full producer attempts then failed
identically while linking the native Simple renderer: integer `.to_i64()` calls
were emitted as references to the unrelated `LogLevel.to_i64` symbol. Adding
`failsafe/core.spl` as an explicit source did not change the result, so another
identical run is forbidden. Three bounded compiler fix/review cycles were
rejected because the candidate could steal resolved enum/trait methods, did
not restore stale inferred-text parse resolution, and included float casts
that direct native selectors cannot implement numerically. The rejected
series is not integrated; the semantic fixture and resume gate are recorded
in `doc/08_tracking/bug/native_primitive_to_i64_ufcs_collision_2026-07-24.md`.
The final producer cycle remains unspent, and no Electron capture or PASS is
admitted from the partial artifacts.

Resume after the exact-current binary and real producer bundle exist:

```sh
SIMPLE_BIN=/absolute/path/to/exact-current-simple \
BUILD_DIR=build/aetheric-host-web-gui-evidence \
sh scripts/check/produce-aetheric-host-web-gui-evidence.shs && \
SIMPLE_BIN=/absolute/path/to/exact-current-simple \
BUILD_DIR=build/aetheric-host-web-gui-evidence \
sh scripts/check/check-aetheric-host-web-gui-evidence.shs
```
