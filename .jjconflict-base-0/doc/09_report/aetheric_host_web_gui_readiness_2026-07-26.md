# Aetheric host Web/GUI proof readiness — 2026-07-26

Status: **POSTPONED as noncritical; no live proof was created.**

User priority now places the pure-Simple WM/GUI/Web/Engine2D chain ahead of
Electron. The strict repository-local Electron 42.5.0 resolver and Aetheric
runtime-identity admission were integrated through `7a03de1b4d`, but no
compiler/provider input was admitted and no Electron process was launched.
The separate WM-event provenance candidate did not pass final review and was
not pushed. TODO 583 remains open at lower priority.

This audit used the sparse linked worktree at `92ae794ba7` and the only
eligible pure-Simple macOS binary:

```text
/Users/ormastes/simple/bin/release/macos-arm64/simple
sha256=277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767
```

Source-only checks passed once:

- `test/03_system/check/aetheric_host_web_gui_evidence_spec.spl`: 4 passed, 0 failed.
- Node syntax for the proof writer and shell syntax for the producer/admission
  wrappers passed.
- The canonical admission wrapper, supplied with the eligible binary but no
  proof, failed as required with `missing-production-proof` before any native
  renderer, Electron, browser, GUI, QEMU, or capture command.

## Post-457 interpreter regression

At clean integration revision `65c6618eb3`, the same pinned `277f8ac9...`
pure-Simple binary (`Simple v1.0.0-beta`) passed:

- `test/unit/lib/common/ui/theme_package_spec.spl`: 11 passed, 0 failed.
- `test/01_unit/app/ui/web_theme_css_authority_spec.spl`: 5 passed, 0 failed.

This covers package/cache/icon lookup, owner-local `UITheme` construction,
BrowserBackend scalar glass colors, canonical package CSS/fingerprint, and
root attributes. It is interpreter-only evidence. It does not prove Cranelift
Option lowering, a current native producer, WM launch, Electron capture or
events, device readback, or QEMU.

## Exact retained prerequisite chain

1. Produce the exact-current proof from the production owner with the eligible
   binary, the exact revision at the eventual producer run, macOS `xcrun`/`nm`,
   and an installed Electron command. The producer builds the generator,
   CPU-SIMD renderer, and UI-access driver; creates SQLite/provider provenance;
   writes the generated Aetheric HTML and Engine2D pixels; then performs the
   single real Electron capture and canonical UI-access actions.
2. The result must be a regular, single-link
   `aetheric-host-web-gui-v1` envelope under its producer `BUILD_DIR`, with all
   referenced generated binaries/artifacts, exact current source revision and
   binary hash, snapshot fingerprints, required glass values, UI action
   history/revisions, nonblank pixels, and all shortcut flags `false`.
3. Feed that same proof to the browser-event wrapper together with the same
   eligible binary and an independently produced Simple Web font-composition
   receipt/run ID. The wrapper pins
   `scripts/check/check-aetheric-host-web-gui-evidence.shs`; no checker override
   is permitted.

## Current unavailable rungs

- No `aetheric-host-web-gui.env` exists in the sparse worktree or the shared
  root build tree, so admission cannot reach artifact validation.
- The sparse worktree deliberately has no local `build/sffi` providers. The
  shared root copies are present and export the required symbols, so a future
  approved producer can pass their explicit absolute paths through
  `AETHERIC_HOST_WEB_GUI_WM_PROVIDER` and
  `AETHERIC_HOST_WEB_GUI_C_WM_PROVIDER`; this audit did not build or copy them.
- `node_modules/electron` is absent in this sparse worktree. `npx` exists, but
  resolving or downloading/running Electron is the next live browser rung and
  was not attempted.
- The eligible `277f` binary reports a version and passes source-only checks,
  but no current-source native build was attempted. Existing state records that
  it cannot import the current compiler graph; it cannot be substituted with a
  seed or another compiler.
- No current producer binaries, provider-provenance manifest, generated HTML,
  CPU-SIMD pixel artifact, Electron capture/screenshot/observation, canonical
  UI-access history, or font-composition receipt exists.

## Resume boundary

Resume this noncritical lane only after the critical pure WM/GUI/Web/Engine2D
plan reaches an appropriate checkpoint and the user explicitly reactivates
TODO 583. Install the pinned dependency without an implicit `npx` download:

```sh
npm ci --prefix tools/electron-shell
```

The strict resolver uses only that worktree-local pinned installation; PATH,
global, `npx`, and network fallback are rejected. Do not fabricate any item
above or run the producer until its admitted inputs exist. The future live
owner must use the canonical command:

```sh
SIMPLE_BIN=/Users/ormastes/simple/bin/release/macos-arm64/simple \
AETHERIC_HOST_WEB_GUI_WM_PROVIDER=/Users/ormastes/simple/build/sffi/libsimple_runtime_wm.dylib \
AETHERIC_HOST_WEB_GUI_C_WM_PROVIDER=/Users/ormastes/simple/build/sffi/libsimple_runtime_c_wm.dylib \
BUILD_DIR=build/aetheric-host-web-gui-evidence \
sh scripts/check/produce-aetheric-host-web-gui-evidence.shs
```

Only after that command produces a retained proof may the pinned admission and
then `check-wm-browser-event-routing-evidence.shs` be considered. This report
claims readiness of source contracts only, never a live rendering PASS.

Compiler-bridge, native CPU-SIMD/Vulkan/Metal comparison, and x86/ARM QEMU
execution are the critical prepared-host work. They remain open and cannot be
replaced or closed by Electron provisioning.
