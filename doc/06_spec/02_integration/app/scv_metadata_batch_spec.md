# SCV bounded metadata batch

AUTHORED MANUAL — UNRUN; not generated executable test evidence.
Source: test/02_integration/app/scv_metadata_batch_spec.spl.
Requirements: REQ-008, REQ-014, REQ-024 (incremental_build_tldr_scv).

1. Two unsaved rows replay with exact quoted/pipe values and contiguous live-owner sequences.
2. Invalid final-row arity leaves earlier rows, WAL bytes and sequence unchanged.
3. WAL destination failure publishes neither rows nor counters, including the legacy insertion path.
4. Empty batch does not create a WAL.
5. Multiline payload and invalid key fail before persistence.
6. Aggregate payload and 4097-row batches fail without a partial write.
7. A torn terminal line is preserved and rejected under the file lease.
8. Failed checkpoint replacement preserves pending entries and counters.

Actual registered/executed/passed/failed/skipped counts: not available.
No source revision, freshness, migration, power-loss or measured speed claim.
