# TODO 652 — Admit Metal MSL ProcessingIR and Drawing Readback on macOS

- Status: open / native row blocked on the current Linux host.
- Target host/hardware: physical Apple Silicon or Intel Mac running macOS with
  a Metal compute-capable GPU. Virtual, CPU-mirror, emulator, and Linux evidence
  cannot satisfy this row.
- Libraries/runtime: Apple `Metal.framework`, `Foundation.framework`, and
  `CoreGraphics.framework`, reached through the repository-owned `objc2-metal`
  runtime provider and the Simple Metal SFFI facade.
- Toolchain: Xcode Command Line Tools exposing `xcrun metal` and
  `xcrun metallib`; admitted source-matched pure-Simple `bin/simple`;
  `SIMPLE_LIB=src`; writable evidence root.
- Exact prerequisite probes: `xcrun --find metal` and
  `xcrun --find metallib`.
- Exact native resume command:
  `SIMPLE_LIB=src bin/simple test test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl --mode=interpreter`
- Exact host-independent performance command:
  `SIMPLE_LIB=src bin/simple test test/05_perf/processing/metal_msl_generation_perf_spec.spl --mode=interpreter`.
- Retained paths:
  - generated `.metal`, `.air`, `.metallib`, hashes, semantic keys, raw
    readback, CPU oracle, mismatch counts, latency, and RSS under
    `build/gpu_renderer_processing_backends/metal_msl/artifacts/`;
  - structured native lifecycle events at
    `build/gpu_renderer_processing_backends/metal_msl/events/native-events.ndjson`;
  - FillRect raw image evidence at
    `build/gpu_renderer_processing_backends/metal_msl/images/fill-rect-readback.rgba`;
  - compiler and system stdout/stderr at
    `build/gpu_renderer_processing_backends/metal_msl/logs/system.log`.
- Required result: FillU32 and Metal-to-Metal drawing source compile; native
  submission succeeds; raw device-origin readback exactly equals the CPU oracle;
  invalid/unsupported translation remains fail-closed.
- Linux unavailable-host result: the host-independent generator row passes,
  both native rows validate this metadata and then call `fail_test`; exit zero
  is forbidden while physical Metal evidence is unavailable.
- Owner: prepared-macOS evidence operator.
- Merge owner and final reviewer: root Codex agent (normal/highest-capability).
