# CUDA Generated Font Handoff

**Status:** conditional release gate; current CUDA device execution unavailable/pending
**Traceability:** REQ-010, REQ-014; NFR-002, NFR-008
**Executable:** `test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl`

> Hand-maintained mirror pending canonical `spipe-docgen`; no generated-manual
> PASS is claimed.

## Operator flow

### Authenticate the source-tracked Simple-generated CUDA font artifact

The scenario loads the compiled-in PTX from
`backend_cuda_font_ptx.spl`, compares its source and emitter-version hashes with
a fresh Simple CUDA emission, recomputes its PTX SHA-256, checks the program
version and exact entry, and proves a one-byte change is rejected. It reads no environment variable,
ignored build artifact, adjacent hash, or package placeholder.

### Prove native submission and device readback

Canonical `Engine2D` CUDA construction installs the tracked bytes only through
`install_cuda_font_artifact` when the active driver accepts them. A rejected
companion leaves primitive CUDA usable but cannot pass this required font
scenario. The scenario submits one 1×1
`FontRenderBatch`, requires `cuda:success`, captures a nonzero device readback
handle, and compares all 16 pixels with the exact 4×4 CPU oracle. CUDA or
artifact unavailability, fallback rendering, stale identity, or any pixel
mismatch fails explicitly.

The default CUDA optimization module still contains no font entry. The tracked
font companion is separate, immutable for the session, and unloaded with the
CUDA context. The checker remains a regeneration/provenance tool; its ignored
outputs are not production inputs.

## Evidence artifacts

- source-tracked `src/lib/gc_async_mut/gpu/engine2d/backend_cuda_font_ptx.spl`
- focused SPipe result and device-origin readback evidence
- optional regeneration output under `build/portable_compute_toolchains/`

The executable spec is authoritative. Regenerate this manual after the
scenario passes and require SPipe docgen to report zero stubs.
