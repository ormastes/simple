<!-- codex-design -->
# Metal MSL Processing Backend Detail Design

The pure generator exposes one Metal-specific lowering function taking
`ProcessingIr` and returning the shared artifact type.  FillU32 emits a stable
preamble, parameter struct, `processing_fill_u32` entry point, explicit buffer
attributes 0/1/2, and a grid-id bounds guard.  Validation precedes emission.

Artifact validation checks target, nonempty source, entry point, ABI marker,
binding list, and semantic key.  Runtime compilation is allowed only after this
validation.  The existing executor will request generated source, compile it,
create a pipeline for the returned entry point, dispatch rounded groups, and
download raw values.  Exact length and element equality are checked against the
CPU oracle before GPU success is admitted.

The shared device probe passes the validated artifact's exact `source` and
`entry_point` into the Metal executor.  The executor compares both with the
canonical deterministic lowering before any device operation, then compiles
that exact source.  It never regenerates and silently substitutes another
shader behind the artifact evidence boundary.

The representative drawing-access value is an in-bounds FillRect with explicit
surface and rectangle extents plus packed `u32` pixel.  Metal-to-Metal lowering
preserves output buffer 0, parameter buffer 2, `uint2` grid coordinates, and
row-major `y * width + x` addressing.  Unknown operations, invalid extents, and
out-of-bounds rectangles emit no source.

The system scenario uses these exact manual steps:

1. Select representative renderer processing kernels
2. Lower shared ProcessingIR for the selected backend
3. Compile and validate the backend artifact
4. Submit native work and capture device readback
5. Compare device readback with the CPU oracle
6. Record unavailable native host evidence

It uses the shared helpers `processing_backend_host_probe`,
`compile_processing_backend_artifact`, `validate_processing_backend_artifact`,
`run_processing_backend_device_probe`, and
`check_processing_backend_oracle_parity`.  No helper may silently succeed.
