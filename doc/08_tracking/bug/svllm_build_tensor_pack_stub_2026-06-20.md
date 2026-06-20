# svllm build_tensor_pack Permanent Stub

**Filed:** 2026-06-20
**Status:** open
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

Open. `build_tensor_pack` is stubbed with `Err(ManifestError.Malformed)` and
the unit spec pins that behavior (`build_tensor_pack (stub — deferred)`).
