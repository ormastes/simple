# Browser Backend Theme + WM Capture Check Progress (2026-07-25)

## Current status

- Repository was synced to `main` and the working head is now at `main@` = `d8b158d1` after pushing the latest theme-id propagation fix.
- Theme rendering fixes now applied in:
  - `src/os/compositor/host_compositor_core.spl`
  - `src/os/desktop/shell.spl`

  Both files now derive WM content theme from the active render snapshot (`active_wm_theme_render_snapshot`) with
  `default_theme_id()` fallback, and pass that theme ID into `simple_web_content_revision_with_theme` / `simple_web_content_frame_cached`.
- Main worktree still has unrelated pre-existing local `doc/` and `.cmd` edits from sibling agent lanes; those are intentionally kept out of this change.

## What was run

- `bin/simple check src/os/compositor/browser_backend.spl` (tooling-level check completed; no file-local syntax failure was reported in browser backend output).
- `jj git fetch`, `jj rebase -d main@origin`, `jj bookmark set main -r @-`, `env -u GITHUB_TOKEN -u GH_TOKEN jj git push --bookmark main`.
- Host/QEMU evidence and renderer checks were executed by side agents:
  - Hosted WM capture evidence script (PASS)
  - ARM64 QEMU readiness checks (PASS)
  - ARM/x86 SIMD checker script (FAIL)
  - x86 render/event check prior to launch (FAIL)

## Evidence files

- `build/agent-qemu-check/hosted/hosted_wm_first_frame.ppm`
- `build/agent-qemu-check/hosted-report.md`
- `build/agent-qemu-check/x86-report.md`
- `build/agent-qemu-check/x86/native-build.out`

## Open blockers

- `check-simpleos-qemu-engine2d-simd-kernels` fails on ARM NEON assertion (`dup vN.4s`) in disassembly check.
- Native build for x86 check fails before QEMU launch in `src/os/compositor/compositor.spl`:
  `_handle_input_backend` cannot infer field type for `left_just_pressed`.
