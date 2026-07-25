# macOS Vulkan/Metal Live Bridge — 2026-07-25 (Current State)

## Objective

Keep Vulkan and Metal host-side 2D evidence paths aligned for same scene, same DPI
capture/receipt semantics, and event ordering; then drive to green once runtime blockers
clear.

## Progress this session

- Fixed `scripts/check/check-macos-gpu-2d-live-evidence.shs` rpath comparison:
  compares canonicalized runtime directory path so `build/sffi` symlinked layouts no
  longer fail `runtime-provider-rpath-missing`.
- Updated `scripts/gui/macos-gui-run.shs` to prefer `bin/release/*/simple` over Rust
  GUI seed as first candidate.
- Verified shell syntax for both updated scripts.
- Re-ran:
  - `scripts/check/check-macos-gpu-2d-live-evidence.shs` (still fails `launched-process-missing`).
  - `scripts/check/check-macos-vulkan-web-live-evidence.shs` (still fails `launcher-failed`).

## Remaining blockers (unchanged by this change)

- Native Vulkan harness still exits before writing receipt in the current host run,
  so live 2D event/window proof cannot yet be established here.
- GUI launch path still fails to produce a stable PID for web proof because the
  executable launched inside the temp `.app` exits without producing the expected
  windowed process.
- The sample program path for web evidence (`web_standards_showcase_gui.spl`) has
  compiler/runtime failures in the current environment (`HIR lowering`/`return` /
  unresolved-name variants depending on execution path).

## Next actions for next lane

1. Investigate native Vulkan process exit path with a direct-instrumented harness
   run to capture the first failing stage and receipt output.
2. Restore a deterministic GUI-launch bridge (self-hosted or seed path) that yields
   a valid launched `SimpleGui` process under macOS LaunchServices.
3. Re-run macOS Vulkan 2D, Vulkan web, and GUI-widget checks after runtime blockers are
   unblocked.
