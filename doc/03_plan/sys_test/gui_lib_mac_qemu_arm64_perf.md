# System Test Plan: GUI Lib macOS + SimpleOS QEMU ARM64 Perf

## Acceptance Target

Prove host GUI sanity, Metal readback, QEMU ARM64 readiness, live or explicitly unavailable QMP capture, deterministic capture comparison, and measured pure-Simple GUI performance.

## Test Phases

1. Host sanity: run native GUI and WM smoke specs without QEMU.
2. Metal sanity: run Metal smoke/readback scripts and record backend identity.
3. QEMU ARM64 readiness: run the ARM64 WM QEMU readiness script and record accelerator availability.
4. Capture: use QMP `screendump` when a socket exists; otherwise record the exact launch/socket prerequisite.
5. Visual comparison: compare captures to existing baselines and emit mismatch metrics.
6. Performance: run graphics and WM perf probes; compare selected metrics to final NFR thresholds after user selection.

## Candidate Commands

- `sh scripts/check/check-metal-generated-2d-readback.shs`
- `sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs`
- `bin/simple test test/perf/graphics_2d/metal_smoke_spec.spl --mode=interpreter`
- `bin/simple run test/perf/graphics_2d/perf_2d_runner.spl --mode=interpreter`
- `sh scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs`
- `sh scripts/check/check-wm-launch-capture-evidence.shs`
- `STRICT_QEMU_CAPTURE=1 QEMU_QMP_SOCKET=<socket> sh scripts/check/check-wm-launch-capture-evidence.shs`

## Pass Criteria

- All selected final requirement IDs have executable test or script evidence.
- Strict lanes fail when required prerequisites are missing.
- Non-strict local lanes record unavailable QEMU/Metal evidence with exact reason.
- Capture reports include dimensions, pixel counts, mismatch counts, checksum, and report path.
- Perf reports include host profile, runtime mode, median or p95 frame/render time, and RSS when available.
