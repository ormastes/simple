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
