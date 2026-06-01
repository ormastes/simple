# GUI Lib macOS + QEMU ARM64 Perf Restart Plan - 2026-06-01

## Current Goal

Continue `$sp_dev check gui lib sanity and perf on mac host, simple os on qemu arm 64, with Metal acceleration` without losing the current hosted-capture work.

## Current Worktree State

- Last pushed baseline before this restart note: `6a434ed5 feat: align wm mdi renderer path`.
- Current local changes are intentionally scoped to hosted WM capture evidence:
  - `src/os/compositor/hosted_wm_capture_evidence.spl`
  - `scripts/check-hosted-wm-capture-evidence.shs`
  - `doc/09_report/hosted_wm_capture_evidence_2026-06-01.md`
- The hosted capture probe now avoids the heavy compositor/WebRender backend import path and uses a local pure-Simple framebuffer plus 8x16 glyph text.
- The capture script validator now accepts both binary `P6` and ASCII `P3` PPM files because the interpreter path produced a zero-byte file for `[u8]` writes.
- `src/compiler_rust/target/debug/simple check src/os/compositor/hosted_wm_capture_evidence.spl` passed after the rewrite.

## Known Incomplete Evidence

- `doc/09_report/hosted_wm_capture_evidence_2026-06-01.md` still records `hosted-wm-capture-timeout` from the last completed report.
- A rerun of `scripts/check-hosted-wm-capture-evidence.shs` was interrupted before completion, so the report must be regenerated before treating hosted capture as accepted evidence.
- Do not claim Metal hosted readback from this probe. It is a bounded CPU/local-pixel evidence probe for the hosted first-frame image while production hosted rendering remains `HostCompositor + simple_web_window_renderer.spl`.

## Resume Commands

```bash
src/compiler_rust/target/debug/simple check src/os/compositor/hosted_wm_capture_evidence.spl
HOSTED_WM_CAPTURE_TIMEOUT_SECS=45 sh scripts/check-hosted-wm-capture-evidence.shs
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/os/compositor/shared_mdi_framebuffer_scene_spec.spl --mode=interpreter --no-cache
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/os/compositor/host_compositor_entry_spec.spl --mode=interpreter --no-cache
find doc/06_spec -name '*_spec.spl' | wc -l
```

## Next Implementation Steps

1. Finish hosted first-frame capture so the report changes from `unavailable` to `pass`, or record the exact remaining failure without hanging.
2. Inspect the generated `build/hosted-wm-capture-evidence/hosted_wm_first_frame.ppm` dimensions and pixel counts; keep the validator thresholds meaningful for real text/window content.
3. Update `doc/09_report/gui_lib_mac_qemu_arm64_perf_initial_evidence_2026-06-01.md` after the capture result is trustworthy.
4. Continue the remaining open gaps from the initial evidence report: Metal benchmark readback hashes, pure-Simple/C perf gap, direct hosted launch first-frame evidence, and QEMU/mac capture comparison.

## Sync Note

This restart plan is safe to commit with the current capture-probe changes as a handoff checkpoint, but it does not close the full GUI/perf goal.
