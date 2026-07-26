# ProcessingIR CUDA/Vulkan Fill64 Parity

- **Status:** open
- **Host:** Linux x86_64 with CUDA and Vulkan devices

## Measured blockers

The source-matched native Vulkan executor passes the existing eight-element
`FillU32(0x01020304)` probe. Expanding the same probe to 64 elements exposed a
size-dependent device result:

```text
completed=true reason=ok values=64
requested_count=64 requested_value=16909060
first_value=135272480 checksum=8657438720 mismatches=64
handle=1 identity=1
```

The requested IR is correct. The first returned value is `0x08101820`, the
aggregate checksum is exactly eight times expected, and all 64 values mismatch.
Importing Engine2D's `_pack_clear_pc` directly into the ProcessingIR executor
then caused a native startup SIGSEGV, consistent with introducing the existing
`backend_vulkan` / `backend_vulkan_helpers` module cycle. The three-cycle
verify/fix cap was reached, so no further live retry was made.

The retained CUDA receipt proves generated CUDA C/PTX and exact device
readback, but it does not call `processing_ir_execute_cuda`. It is valid
lower-level evidence, not ProcessingIR backend parity evidence.

A new direct CUDA native probe initially failed at module load because the
Simple wrapper passed native text to C-string runtime entry points. Routing
compiled calls through the existing length-tracked PTX and kernel-name ABIs
fixed module load and launch. CUDA then completed device readback but returned
the same 64 mismatches and checksum `8657438720` as Vulkan. Its native identity
was negative despite the runtime's positive 63-bit contract. Exact-size result
array allocation did not change either result and was removed. This narrows the
shared defect to scalar/device-buffer transport rather than array growth or one
backend shader.

## Required repair

1. Move the clear push-constant packer to an acyclic shared module, or reproduce
   its value-return/reassignment semantics locally without importing the
   Engine2D backend-helper cycle.
2. Compare raw device bytes before Simple `u32` conversion and inspect native
   scalar argument packing; both direct backends currently show 64 mismatches
   and an aggregate checksum multiplied by eight.
3. Repair the native CUDA identity ABI without masking or fabricating failed
   identity `0`.
4. Normalize the existing direct CUDA probe and the Vulkan probe on the same
   64-element fill after the transport repair.
5. Require exact count/value/checksum, zero mismatches, device readback,
   positive backend provenance, no CPU fallback, and source-matched freshness
   from both probes before publishing a unified parity receipt.

Retained build logs:

- `build/simpleos_gpu_host/vulkan_fault_native/build-parity64.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-parity64-cycle2.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-parity64-cycle3.log`
- `build/simpleos_gpu_host/cuda_fill_native/build-cycle3.log`

No compiler bootstrap was run.
