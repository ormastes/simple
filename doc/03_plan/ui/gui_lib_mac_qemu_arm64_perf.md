# Agent Task Plan: GUI Lib macOS + SimpleOS QEMU ARM64 Perf

## Team A: Local Evidence Inventory

- Confirm source ownership for `src/os/gui`, `src/os/compositor`, `src/os/desktop`, Engine2D, Metal SFFI, and QEMU capture modules.
- Map each acceptance criterion in `.spipe/gui-lib-mac-qemu-arm64-perf/state.md` to an executable command or missing prerequisite.
- Output: update `doc/01_research/ui/gui_lib_mac_qemu_arm64_perf.md` with evidence deltas only.

## Team B: macOS Host + Metal Sanity

- Run Metal smoke/readback specs and scripts on the macOS host.
- Record device/backend identity, runtime mode, frame/readback timing, command result, and report path.
- Investigate failures in `metal_session.spl`, `metal_sffi.spl`, or Engine2D session code.

## Team C: SimpleOS QEMU ARM64 Lane

- Run `scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs`.
- Launch or attach to QEMU ARM64 with HVF when available.
- Produce QMP `screendump` capture evidence and record QEMU binary, accelerator, display backend, socket path, and image path.
- Keep the ARM64 dock on real procedural icon rendering, not placeholder letters; the live screendump assertion should detect icon artwork detail in the framebuffer.

## Team D: Capture Compare + Drawing Consistency

- Normalize host and QEMU captures to deterministic dimensions and pixel format.
- Compare against `test/09_baselines/*` and emit mismatch count, first mismatch coordinate, checksum, and markdown report.
- Triage mismatches into expected platform variance, baseline drift, renderer bug, or capture bug.

## Team E: Pure-Simple Perf Optimization

- Run `test/05_perf/graphics_2d/perf_2d_runner.spl`, `test/02_integration/rendering/perf_smoke_spec.spl`, and WM perf specs.
- Identify hot paths in pure `.spl` Engine2D/WM/render code.
- Implement only after selected feature and NFR options define target thresholds.

## Team F: Verification + Docs

- Generate or update SPipe specs only under `test/**`.
- Generate mirrored `doc/06_spec/**/*.md` manuals after spec changes.
- Ensure `find doc/06_spec -name '*_spec.spl' | wc -l` remains `0`.
