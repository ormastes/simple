# Metal MSL Renderer Processing Backend

This executable scenario proves the host-independent Metal artifact contract
and keeps native execution visibly blocked on hosts without Metal.

## Primary flow

1. **Select representative renderer processing kernels** — choose canonical
   FillU32 and stride-aware FillRect ProcessingIR values.
2. **Lower shared ProcessingIR for the selected backend** — produce a
   deterministic `metal-msl` artifact with semantic identity.
3. **Translate drawing access for the destination backend** — preserve output
   buffer 0, unused buffer 1, parameters buffer 2, two-dimensional coordinates,
   stride-aware row-major indexing, and packed pixels.
4. **Compile and validate the backend artifact** — reject missing, invalid,
   unsupported, or stale semantic artifacts before native work.
5. **Submit native work and capture device readback** — on macOS, execute the
   exact validated artifact source and entry point, reject any mutation before
   device access, and require positive stable device provenance.
6. **Compare device readback with the CPU oracle** — require exact values and
   pixels; tolerance and CPU-mirror evidence are forbidden.
7. **Record unavailable native host evidence** — on Linux the executable row
   emits `status=blocked` and verifies TODO 652's prerequisites, exact resume
   command, retained artifacts, owner, and final reviewer, then fails the native
   examples explicitly. It cannot be counted as native Metal PASS evidence.

## Evidence admission

- Host-independent artifact generation may pass on Linux.
- Native FillU32 and FillRect examples use `fail_test` when Metal is unavailable.
- A green complete scenario therefore proves the exact validated artifact was
  compiled, submitted, read back from a positive Metal device identity, and
  compared byte-for-byte with the independent CPU oracle.
- CPU fallback, regenerated substitute source, tolerance, missing provenance,
  or an unsupported/lossy translation cannot satisfy admission.

## Native resume

`SIMPLE_LIB=src bin/simple test test/03_system/app/simple_2d/feature/processing_metal_msl_backend_spec.spl --mode=interpreter`

See `doc/08_tracking/todo/gpu_renderer_processing_metal_native_macos_2026-08-02.md`.

The native operator must use a physical Apple Silicon or Intel Mac with a
Metal compute GPU, Apple Metal/Foundation/CoreGraphics frameworks, Xcode
Command Line Tools (`xcrun metal` and `xcrun metallib`), and an admitted
source-matched pure-Simple binary. Evidence is retained beneath
`build/gpu_renderer_processing_backends/metal_msl/`: compiled inputs/outputs
under `artifacts/`, structured lifecycle events under
`events/native-events.ndjson`, FillRect raw image evidence under
`images/fill-rect-readback.rgba`, and compiler/system output under
`logs/system.log`. Admission requires a positive physical device identity and
handle, raw device-origin readback exactly equal to the CPU oracle, zero
mismatches, and no CPU fallback.

## Host-independent NFR gate

Run `SIMPLE_LIB=src bin/simple test test/05_perf/processing/metal_msl_generation_perf_spec.spl --mode=interpreter` with the admitted pure-selfhost binary. It requires 512 deterministic generations, average latency below 10 ms, procfs `VmHWM` incremental peak RSS below 8 MiB, and semantic-key invalidation for changed ProcessingIR values/counts. Seed-runner measurements are diagnostic only.

## Emulator preparation

The host-independent `metal_emulator_spec.spl` proves CPU upload, exact-artifact
validation, bindings 0/1/2, emulated dispatch, raw download, FillRect oracle
parity, repeat reuse, and invalid binding/source/entry/transfer rejection. Every
receipt is marked `evidence_class=emulator` and `native_device=false`.

The retained unit evidence follows the frozen operator flow exactly:

1. `Probe backend environment and wrapper ownership`
2. `Upload CPU input through the HAL`
3. `Dispatch offloaded GPU rendering logic`
4. `Download GPU output through the HAL`
5. `Verify communication and rendering parity`
6. `Classify physical emulated and blocked evidence`

The machine-readable receipt is retained at
`build/test-artifacts/01_unit/lib/gc_async_mut/processing/metal_emulator/evidence.env`.
It records the evidence class, native-device classification, runtime/HAL/device
identity, validator and memory capabilities, transfer/dispatch state, exact
bindings, counts, parity, and terminal reason.

Emulator evidence prepares REQ-013/015 and NFR-007 but never promotes the native
row. On macOS the semantic scenario still invokes the exact native Metal
executor, requiring compiled MSL, submission, device-origin readback, positive
identity, and exact CPU-oracle parity.
