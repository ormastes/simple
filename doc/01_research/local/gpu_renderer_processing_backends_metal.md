<!-- codex-research -->
# Metal MSL Processing Backend — Local Research

The repository already owns a validated `ProcessingIr` FillU32 value and CPU
oracle in `src/lib/common/processing/processing_ir.spl`.  The production Metal
executor in `src/lib/gc_async_mut/processing/metal_fill_u32.spl` compiles and
dispatches MSL through the canonical Metal SFFI, preserves typed failures, and
returns device identity plus raw values.  Its shader is currently a monolithic
`PROCESSING_METAL_MSL` constant, however, so it cannot produce a shared backend
artifact, expose deterministic cache identity, or reject unsupported semantics
at a generator boundary.

Existing macOS scenarios prove the intended native path: compile library,
create compute pipeline, dispatch, wait, download, and compare exact raw values.
On Linux, `processing_ir_metal_valid_unavailable_spec.spl` correctly reports
`metal-unavailable`; it is evidence of fail-closed behavior, not GPU execution.

The narrow implementation seam is therefore a pure generator module beside the
executor.  It consumes validated `ProcessingIr`, emits deterministic MSL and a
stable semantic key, and is adapted to the shared backend artifact contract.
The executor then consumes generated source without changing the renderer API.
