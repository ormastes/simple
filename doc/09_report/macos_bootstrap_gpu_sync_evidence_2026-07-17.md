# macOS bootstrap and GPU sync evidence — 2026-07-17

Host: Apple Silicon arm64, macOS, platform triple `aarch64-apple-darwin`.

## Bootstrap

- `scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift` passed.
- Stage 2 passed bootstrap compiler sanity; SHA-256: `33d74e9935b8f9afc2e8b718c4b562d953243d270b0667853f91fe71331d11ee`.
- Stage 3 passed bootstrap compiler sanity; SHA-256: `45c4d47d75b7690b8e5cc08e550f6a1ae84de1ac4d779117e797d0965a18a793`.
- Artifacts are Mach-O 64-bit arm64 executables under `build/bootstrap/stage{2,3}/aarch64-apple-darwin/simple`.
- The LLVM attempt correctly failed because the existing Rust seed was built without the LLVM feature; no Rust seed was substituted as production tooling.

## Full CLI boundary

The verified Stage 3 compiler was used for the exact Stage 4 `main.spl` entry with `--runtime-bundle core-c-bootstrap`, Cranelift, an isolated cache, and one-binary mode. The process remained CPU-active for approximately ten minutes, peaked near 7.5 GB RSS, emitted no object/cache files or diagnostics, and was stopped at the mandatory runaway ceiling. No retry was made. This leaves the provider-capsule work in TODO 535 and the Intel-host half of TODO 531 open.

## Metal web/GUI evidence

- Canonical surfaced browser Draw IR rendered four commands through Metal with zero skipped commands.
- Readback provenance was `device_readback`; all 76,800 pixels were nonblank.
- Artifact: `build/macos-metal-browser-backing/simple-typed-full-target.argb.json`.
- Chrome and Electron Metal backing both passed and matched each other exactly.
- The deployed July 5 full CLI remains too old for current Metal encoder externs, so the aggregate Simple/Chrome/Electron gate cannot close until a current full CLI can be deployed.

## Fresh gate refresh after parser hardening

- The Stage4 first-file `Map.keys` SIGBUS was fixed by constructing bootstrap
  frontend maps with `Map.new()`. A later generic-type closing `>` no longer
  swallows the following class dedent; the T32 mini closure and full CLI closure
  both passed the former `t32_cli/types.spl` parse failure.
- The exact full closure then exposed duplicate physical sources in phase 2.
  After 750.8 seconds only 202 of 2,095 parse entries had completed, with many
  consecutive duplicate paths, so the run was stopped under the runaway guard.
  The blocker and acceptance criteria are tracked in
  `doc/08_tracking/bug/stage4_entry_closure_duplicate_parse_2026-07-17.md`.
- Fresh Chrome and Electron captures both used ANGLE Metal on Apple M4 and
  matched bit-exactly at 320x240: 76,800 nonblank pixels and checksum
  `329775811848360` each.
- The Simple side remains fail-closed on the deployed CLI: portable Metal
  emission and framebuffer evidence stop at `rt_cli_arg_count`; current
  CPU/Metal and browser rendering stop at the missing
  `rt_metal_destroy_compute_encoder` extern.
- Building the GUI-feature host driver exposed a stale `Arc<String>` to
  `String` conversion in winit SFFI. The conversion was fixed and the documented
  GUI driver build completed in two minutes.
- The shared-MDI titlebar contract passes. The live sample emitted its full MDI
  protocol but did not leave an Aqua window. The evidence wrapper also allowed
  the launcher's AppleScript nudge to block before its own deadline; the wrapper
  now disables that redundant nudge so bounded window discovery owns the
  timeout. No live-window PASS is claimed.
