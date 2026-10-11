# Shared SourceChange contracts v1

This is WP1 within all 28 selected incremental TLDR/SCV/build requirements. It does not replace the selected 2026-10-08 design or narrow its acceptance matrix.

`src/lib/common/source_change/contracts_v1.spl` owns pure value carriers: `EditOriginV1`, `SourceSaveStateV1`, `SourceEditV1`, `SourceChangeBatchV1`, `SourceFileCaptureV1`, `SourceSnapshotV1`, `SourceChangeLimitsV1` and `SourceChangeShapeV1`. Wire-facing schema and sequence/byte positions retain u32/u64 widths. Snapshots carry byte-owner/generation tokens, complete inventory identity, digest and path policies, save state and captured file bytes. Those fields are claims requiring admission; this module does not mint a new compiler root algorithm.

Shape validation checks schema, nonzero sequence, canonical SHA-256 spelling via the existing common owner, slash-relative path spelling, nonempty identities, unsigned coordinate bounds, edit cardinality and cumulative replacement-size claims. Its metadata budget covers the three root strings plus all per-edit text fields; count bounds separately bound fixed record overhead. Per-field and remaining-budget checks precede subtraction. A transaction ID equal to its path still receives its independent identity bound.

A well-formed incomplete batch remains a hint. `complete=true` is also an untrusted field: shape validity does not verify content digests, generation lifetime/continuity, normalized path ownership, per-file edit ordering, complete inventory or durable publication. No `ValidatedChangeV1`, revision or freshness receipt is produced here. The complete transition validator, shared codecs, adapters, existing SCV WAL owner and compiler all-domain snapshot/root admission remain required.

The existing exact-byte primitive remains owned by the original incremental worktree. It is not copied or reimplemented in this isolated contracts lane. Subsequent integration must reuse it and preserve original-snapshot coordinates.

Five authored SSpec scenarios share sixteen cases with a native diagnostic. The SSpec is UNRUN. The native probe compiles, but the admitted historical producer fails its first returned text-field check. The explicit type/import control also fails, so neither inference-only causation nor valid contract execution is established. Three native cycles are closed; do not replay this producer unchanged.
