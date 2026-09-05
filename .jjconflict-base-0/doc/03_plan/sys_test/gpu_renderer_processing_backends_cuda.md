# GPU Renderer Processing Backends — CUDA System Test Plan

## Scope

CUDA FillU32 generation/compile/readback, CUDA drawing-access translation to
Vulkan and DirectX, exact-entry bootstrap resumption, and fail-closed evidence
admission. Merge owner and final reviewer: root Codex agent at normal/highest
capability.

## Traceability

| Requirement | Executable evidence | Pass condition |
| --- | --- | --- |
| AC-1 | `cuda_fill_u32_validation_spec.spl`, `processing_cuda_backend_spec.spl` | CUDA consumes shared `ProcessingIR` and returns shared artifact/evidence types. |
| AC-3 | canonical CUDA wrapper contract | Source-matched PTX executes with positive device provenance and exact CPU-oracle parity; missing candidate remains blocked. |
| AC-6 | CUDA validation/drawing/system specs | Invalid IR, unsupported operations/targets, missing compiler identity, malformed receipts, and absent probes fail closed. |
| AC-7 | focused unit specs plus two system specs/manuals | Generation, semantic invalidation, submission admission, provenance, parity, and unavailable rows are visible. |
| AC-8 | architecture, backend guide, CUDA operator manual | Contracts, cache invalidation, backend evidence, resume commands, and blockers stay current. |
| AC-10 | exact-entry loader regression and final root review | Only owned files change; exact `/test/` entry exception does not admit the test tree broadly. |
| AC-11 | `cuda_drawing_translation_spec.spl` | Vulkan artifact carries real SPIR-V binary; DirectX preserves `u0`/`b0`, row-major addressing, half-open coordinates, and packed `u32`. |
| AC-12 | `processing_cuda_directx_native_spec.spl`, TODO 653 | Host-independent HLSL contract passes; native Windows row stays open until physical-device raw readback matches the oracle. |
| REQ-013 | `processing_cuda_hal_live_spec.spl` | Simple runtime loads libcuda, creates a real context/module, uploads CPU input, dispatches PTX, and downloads exact device output. |
| REQ-014 | `processing_cuda_hal_live_spec.spl` | Two dispatches retain positive stable device identity/module and match `[8,9,17,107]`; invalid transfers reject. |
| NFR-007 | retained `PROCESSING_CUDA_HAL` receipt | Physical CUDA HAL evidence names device origin, stable provenance, exact parity, repeated dispatch, and `cpu_fallback=false`. |

## Cases

1. Happy: deterministic CUDA PTX artifact has the real FillU32 entry/body and
   semantic key; exact device readback is admitted only with positive identity.
2. Edge: drawing stride exceeds width; half-open rectangle writes only the
   selected row-major pixels.
3. Error: invalid extent/rectangle, non-drawing translation, CUDA-to-Metal,
   missing compiler identity, CPU-mirror provenance, and oracle mismatch reject.
4. Bootstrap: an exact `/test/` entry is admitted while sibling test files stay
   filtered; stale interpreted-worker bootstrap is not closure progress.
5. Unavailable: missing source-matched CUDA candidate and Windows DirectX host
   remain blockers with exact resume commands and retained-artifact lists.

## Focused commands

```sh
bin/simple test test/01_unit/lib/gc_async_mut/processing/cuda_fill_u32_validation_spec.spl --mode=interpreter
bin/simple test test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/driver/native_build_explicit_test_entry_filter_spec.spl --mode=interpreter
bin/simple test test/03_system/app/simple_2d/feature/processing_cuda_backend_spec.spl --mode=interpreter
bin/simple test test/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/simple test test/02_integration/rendering/processing_cuda_hal_live_spec.spl --mode=interpreter
```

Do not invoke the blocked native build during this preparation lane. When TODO
651 is cleared, run each canonical native wrapper once against the produced
source-matched candidate.
