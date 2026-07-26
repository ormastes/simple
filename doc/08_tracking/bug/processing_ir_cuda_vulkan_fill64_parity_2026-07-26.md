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
the same 64 mismatches and checksum `8657438720` as Vulkan. Exact-size result
array allocation did not change either result and was removed.

The focused native `processing_u32_array_transport_probe.spl` isolated the
shared result:

```text
case=local-push  first=135272480 iterator_mismatches=0 indexed_mismatches=64
case=local-fixed first=135272480 iterator_mismatches=0 indexed_mismatches=64
case=returned    first=135272480 iterator_mismatches=0 indexed_mismatches=64
case=wrapped     first=135272480 iterator_mismatches=0 indexed_mismatches=64
```

Iteration decodes all 64 host-generated values exactly while direct indexing
returns each tagged integer (`value << 3`). Disassembly confirms iteration calls
`rt_index_get` and untags its result, while direct indexing loads tagged array
storage without an untag. This reproduces the 8x symptom without a GPU and
narrows the blocker to the retained compiler's native read path. It does not
prove that CUDA/Vulkan device bytes were correct.

Current source marks array parameters as runtime arrays and routes that path
through `rt_array_get` plus `decode_runtime_value`; built-in `u32` is already a
primitive HIR type, so the earlier proposed struct-provenance guard was
withdrawn. A fresh source-matched compiler is required to determine whether the
retained compiler is stale or current lowering still loses runtime-array
classification.

CUDA identity was a separate three-bit tag-width overflow: the UUID hash used
the full positive 63-bit range, so native Simple tagging could make it negative.
The Rust runtime and generated C evidence producer now share a positive 60-bit
mask. The focused native Simple probe passes with identity
`1002905313239842438`, and the live generated CUDA checker reports two distinct
positive identities plus exact fill/copy/alpha/scroll device readback.
This width change intentionally changes previously recorded 63-bit identities;
cross-version receipts and identity-keyed caches must not compare old and new
values as the same algorithm version.

## Required repair

1. Regenerate a source-matched pure-Simple compiler incrementally on an admitted
   host; do not run a full bootstrap.
2. Run the focused transport probe once with that compiler and require zero
   iterator and indexed mismatches for all four recorded cases.
3. Re-run the direct CUDA and Vulkan 64-element probes with that compiler.
4. If direct indexing still loads raw storage, trace the lost runtime-array
   classification and repair the shared Index lowering before backend retries.
5. Require exact count/value/checksum, zero mismatches, device readback,
   positive backend provenance, no CPU fallback, and source-matched freshness
   from both probes before publishing a unified parity receipt.

Retained build logs:

- `build/simpleos_gpu_host/vulkan_fault_native/build-parity64.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-parity64-cycle2.log`
- `build/simpleos_gpu_host/vulkan_fault_native/build-parity64-cycle3.log`
- `build/simpleos_gpu_host/cuda_fill_native/build-cycle3.log`
- `build/simpleos_gpu_host/u32_transport/processing_u32_array_transport_probe`
- `build/simpleos_gpu_host/cuda_identity/cuda_device_identity_probe`
- `doc/09_report/cuda_generated_2d_readback_2026-07-26.md`

No compiler bootstrap was run.
