# CUDA Generated Font Handoff

**Status:** fail-closed stale-artifact evidence; native CUDA promotion pending regeneration
**Traceability:** REQ-010, REQ-014; NFR-002, NFR-008
**Executable:** `test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl`

> Hand-maintained mirror pending canonical `spipe-docgen`; no generated-manual
> PASS is claimed.

## Operator flow

### Reject the stale source-tracked CUDA font artifact

The scenario loads the compiled-in PTX from `backend_cuda_font_ptx.spl`, proves
its retained PTX SHA-256 is intact, and compares it with the corrected common
straight-ARGB emitter. ABI program version remains `1`; common compositor
semantics are revision `2`, while the retained PTX is explicitly revision `1`.
The trust gate therefore rejects both the exact stale bytes and tampered bytes.

### Restore native submission and device readback

Canonical `Engine2D` construction now refuses to install the stale companion,
while primitive CUDA remains usable. Native font submission and exact CPU pixel
parity must be restored only after an admitted pure-Simple emitter regenerates
the CUDA source, PTX, hashes, and semantics revision. Tool-only regeneration is
not accepted as source provenance.

The default CUDA optimization module still contains no font entry. The tracked
font companion is separate, immutable for the session, and unloaded with the
CUDA context. The checker remains a regeneration/provenance tool; its ignored
outputs are not production inputs.

## Evidence artifacts

- source-tracked `src/lib/gc_async_mut/gpu/engine2d/backend_cuda_font_ptx.spl`
- focused SPipe stale-artifact rejection result
- optional regeneration output under `build/portable_compute_toolchains/`

The executable spec is authoritative. Regenerate this manual with the admitted
SPipe docgen; no CUDA device-origin font readback PASS is currently claimed.
