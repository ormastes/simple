# CUDA-to-DirectX Native Evidence Admission

## Purpose

Keep CUDA drawing-access translation to DirectX testable on every host while
making native Windows execution an explicit blocker until retained physical-
device readback matches the shared CPU oracle.

## Flow

1. **Select representative renderer processing kernels** — select the shared
   FillRectU32 drawing operation.
2. **Translate drawing access for the destination backend** — generate HLSL
   with output UAV `u0`, parameter buffer `b0`, row-major
   `py * stride + px`, half-open rectangle bounds, and exact packed `u32`
   pixels.
3. **Compile and validate the backend artifact** — reject non-drawing IR and
   unsupported/lossy destination translations. On Windows x86_64, require the
   Windows SDK D3D12 runtime/debug layer and DXC on `PATH`; compile and retain
   HLSL, DXIL, logs, versions, diagnostics, identities, hashes, and semantic
   key.
4. **Submit native work and capture device readback** — require a physical
   DirectX 12 compute adapter (never WARP), positive backend/resource handles,
   adapter feature level, command-list/queue submission, completed fence, clean
   debug-layer events, rendered image dimensions/format/hash, and raw
   device-origin output. Source validation alone remains blocked.
5. **Compare device readback with the CPU oracle** — require equal lengths,
   zero mismatches, and exact untouched/filled pixels including padded stride.
6. **Record unavailable native host evidence** — keep TODO 653 open and run:

   ```sh
   SIMPLE_LIB=src bin/simple test test/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.spl --mode=interpreter
   ```

The current scenario passes the host-independent artifact and blocker contract.
It does not report native DirectX execution PASS on Linux. After validating the
resume metadata, the executable native row deliberately calls `fail_test` with
`BLOCKED CUDA-to-DirectX native row`; therefore an unavailable Windows host is
visible as a release-blocking failure rather than a green documentation check.
The prepared-Windows evidence operator owns collection; the root Codex agent is
merge owner and a normal/highest-capability Codex reviewer gives final approval.
