# CUDA ProcessingIR Backend Operator Flow

## Purpose

Qualify CUDA FillU32 generation and device-readback provenance through the
shared `ProcessingIR` contract, plus CUDA drawing-access translation to Vulkan
and DirectX. Host-independent DirectX source checks are not native DirectX
execution evidence.

## Scenario

1. **Select representative renderer processing kernels** — use FillU32 for the
   native CUDA path and FillRectU32 for drawing translation.
2. **Lower shared ProcessingIR for the selected backend** — require a valid
   `ProcessingBackendArtifact` with target `CudaPtx`, entry
   `processing_fill_u32`, semantic key, and non-placeholder PTX body.
3. **Translate drawing access for the destination backend** — preserve output
   binding 0, parameter binding 0, row-major `py * stride + px` addressing,
   half-open rectangle bounds, and exact packed `u32` pixels. Reject non-drawing
   IR and CUDA-to-Metal requests as unsupported rather than approximating them.
4. **Compile and validate the backend artifact** — a compiler failure or absent
   compiler identity remains failed evidence. PTX driver module loading is the
   runtime validator; DirectX uses DXC on the prepared Windows row.
5. **Submit native work and capture device readback** — build the source-matched
   Simple probe, then run `sh scripts/check/check-processing-cuda-fill-native.shs`.
   A receipt must name `device_readback`, positive device provenance, and
   `cpu_fallback=false`.
6. **Compare device readback with the CPU oracle** — require every returned
   element and checksum to match. Missing provenance or any mismatch fails
   closed and returns no admissible values.
7. **Record unavailable native host evidence** — Windows DirectX remains open
   under TODO 653. On the prepared host run exactly:

   ```sh
   SIMPLE_LIB=src bin/simple test test/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.spl --mode=interpreter
   ```

## Current blockers

- The Linux NVIDIA host has suitable devices and `nvcc`, but the canonical
  source-matched Simple CUDA probe binary is absent. TODO 651 blocks its native
  build; `probe-binary-missing` is a blocker, never a PASS.
- Native DirectX execution requires the prepared Windows capability in TODO
  653. Linux HLSL assertions prove only artifact and binding shape.

## Fail-closed scenarios

- A missing executable at the canonical probe path reports
  `processing_cuda_fill_native_status=blocked` with
  `processing_cuda_fill_native_reason=probe-binary-missing` and exits nonzero.
  This is not GPU execution evidence even when `nvidia-smi` sees a device.
- A receipt must occur exactly once and match the exact count, checksum,
  device-readback provenance, positive handle/identity, and
  `cpu_fallback=false`; malformed or duplicate receipts fail.
- Explicit native-build entries below `/test/` are admitted only when they are
  the exact `SIMPLE_NATIVE_BUILD_ENTRY`. Other test trees remain filtered.
- The retained stale-seed build timed out while interpreting the full worker
  compiler/LLVM graph before closure traversal. Resume only with the traced
  TODO 651 command on an admitted compiled pure-Simple CLI; do not increase the
  timeout or count warning output as closure progress.
- CUDA-to-Vulkan drawing requires a nonempty validated SPIR-V binary. CUDA-to-
  DirectX requires deterministic HLSL with `u0`/`b0` bindings; neither artifact
  alone proves device execution.

## Windows DirectX row

TODO 653 remains open until the prepared Windows host retains generated HLSL
and DXIL, DXC identity/logs, physical adapter identity, positive backend handle,
raw device-origin readback, CPU-oracle output, and zero mismatches. Run the
exact system spec command shown above; the scenario validates admission and
blocker visibility but cannot turn absent native evidence into PASS.
