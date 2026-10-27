# SCVN-B03 storage lane design

This is the first implementation slice of the approved full SCV plans, not a
replacement scope or a completed B03 acceptance report. Shared contracts and
the phase-2 architecture/design remain owned by the parent integration lane.

`scv_content_id_for_file_checked` returns `Result<text, text>`; the original
function delegates with the same Result signature. A failure has no content
identity. Actual content-producing callers match Ok/Err; integrity predicates
compare only to `Ok(expected_id)`, so two failed reads cannot establish equality.

`ScvFileBuffer` retains its existing representation. The regular-file,
no-follow, bounded-byte provider performs the single payload read. Pre-read
size admission and post-read length validation reject oversized or changed
captures. Missing, inaccessible, nonregular and symlink inputs are explicit
errors. Content-id and publication methods check `buffer.error` and return
Results. Successful captures keep legitimate empty files and exact bytes.

Byte chunks publish through `atomic_write_bytes`, which uses the existing
typed secure-temp-directory facade to exclusively create a private stage in
the destination parent. It exclusively creates its own payload, writes/syncs
that payload and atomically renames it into place. Only owned staging paths
are cleaned; arbitrary destination `.tmp` and `.lock` neighbors are never
used. Whole-payload replacement needs no shared read/modify lock. Text
publication retains its bool API and removes the non-atomic fallback. Existing
chunks are verified before deduplication. Snapshot creation checks each owned
object, WAL, mutable-head/workspace, status-index and event acknowledgement.

The WAL BEGIN/SET/NEW recovery record is staged as one append before root
publication. A partial root failure leaves the record pending rather than
falsely writing ABORT. Recovery checks its own writes before acknowledging
forward/rollback success; snapshot rejects recovery errors.

Annotated-tag import checks the object writer's error outcome before either
reference update. Reference setters report failed writes, and annotated
references reject unsafe/nonexistent tag object identities. This does not
establish a transaction spanning both tag references.

The public structural matcher imports remain compatible through explicit
exports after splitting shared values and source/CST adapters. Checkpoint
integrity and stored-block gzip helpers have narrow owners to keep modified
files below 800 lines. Existing CDC boundaries and identity payloads remain
the same for successful captures.

Open qualification: native provider support, Result/tuple compilation, test
execution, generated-manual review, read-once I/O measurements, actual grow
races, sync failures and crash/power-loss recovery. Parent-directory fsync,
repository-wide writer serialization, transactional change-pointer publication,
multi-file snapshot barriers and all remaining legacy metadata-read/write
callers are not established by this slice.
