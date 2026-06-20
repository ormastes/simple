# svllm build_tensor_pack Permanent Stub

**Filed:** 2026-06-20
**Resolved:** 2026-06-20
**Status:** resolved (Option 1 implemented)
**Priority:** P2

## Problem

`build_tensor_pack(pack_root, m)` always returns `Err(ManifestError.Malformed)`.
It cannot reconstruct a `TensorPack` from a `TensorPackManifest` because
`TensorPackManifest` carries only counts (`tensor_count`, `chunk_count`), not
the full per-tensor/chunk lists needed to rebuild the descriptor.

## Root Cause

`parse_manifest` is a scalar-field extractor: it searches for key markers and
counts array entries but does not parse individual `TensorInfo` or `ChunkInfo`
objects. `TensorPackManifest` was designed to hold summary metadata only
(schema, model_id, revision, preferred_chunk_bytes, counts). There is no
representation path from manifest text → full tensor/chunk lists.

## Fix Options

1. **Enrich TensorPackManifest**: add `tensors: [TensorInfo]` and
   `chunks: [ChunkInfo]` fields; extend `parse_manifest` to populate them by
   fully parsing each array element. `build_tensor_pack` then copies them
   directly into a `TensorPack`.
2. **Separate parse phase**: introduce a second function
   `parse_manifest_full(sdn_text) -> Result<TensorPack, ManifestError>` that
   parses the complete structure in one pass, bypassing `TensorPackManifest`
   for the materializer path. The scalar-only `parse_manifest` remains for
   fast header validation.

Option 1 is the lower-risk path; Option 2 avoids bloating `TensorPackManifest`
and keeps the existing API surface stable.

## Status

Resolved 2026-06-20 via **Option 1**. `TensorPackManifest` now carries
`tensors: [TensorInfo]` and `chunks: [ChunkInfo]`; `parse_manifest` parses each
array element into those lists, and `build_tensor_pack` constructs a `TensorPack`
from them while validating invariants (chunk_id in range, `offset_in_chunk`/
`byte_len` fit within the referenced chunk, tensors-without-chunks rejected) —
returning `Err(ManifestError.TensorChunkMismatch)` on violation. Covered by
`manifest_spec.spl` (full round-trip + validation-failure tests) and
`test/03_system/tools/svllm_build_tensor_pack_system_spec.spl`.
