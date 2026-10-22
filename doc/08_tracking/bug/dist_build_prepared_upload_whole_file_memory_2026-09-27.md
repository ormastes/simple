# Prepared upload materializes a whole input file in memory

Status: source repair drafted; executable memory evidence pending. Priority: P1.
Owner: Codex root with the parallel transport implementation agent.

Static reproducer: `_snapshot_put_v1` in
`src/app/build/scheduler/prepared_upload.spl` calls
`file_read_regular_no_follow_bounded_bytes` with a 256 MiB per-file limit,
then holds the entire returned array while `file_write_bytes` writes the
prepared snapshot. A two-worker wave can hold multiple such arrays while the
scheduler is supposed to enforce a bounded memory budget. This is reachable
with otherwise valid large binary inputs; digest checks do not reduce the
peak allocation.

Repair in Simple: open the source through the existing descriptor-pinned
beneath-root file view, reject sizes above the per-file and remaining total
limits before reading, then copy and hash in 1 MiB chunks through a scoped
file handle. Close both handles on every path; verify the staged size and
digest after writing. Keep the existing private snapshot and canonical SFTP
batch protocol. Do not add a C copy engine.

Evidence: a focused binary fixture larger than one chunk must preserve exact
bytes and digest; wrong digest, oversize, symlinked ancestor, and copy failure
must fail closed. The source-matched Simple runner and peak-memory fixture
remain required before claiming the N2 memory target.

Boundary audit: the self-hosted C `rt_file_hash_sha256` streams through a
fixed buffer, while the Rust runtime twin currently calls `std::fs::read`
before hashing. The streaming Simple snapshot copy does not establish a
cross-runtime peak-memory claim until that twin is repaired or explicitly
excluded by an admitted runtime provenance rule.

The drafted Simple repair opens each source or CAS blob beneath its explicit
root, rejects the pinned size before reading, and copies through a 1 MiB
buffer while hashing. A binary fixture crosses the chunk boundary and checks
wrong-digest rejection. The focused spec is unrun under this session's
self-hosted verification cap, so this bug remains open.

Cleanup follow-up: a failed snapshot preparation now retains its private root
when removal fails. The parent returns that exact root with a reconciliation
flag, and `release_prepared_build_request_v1` can retry removal even when the
preparation was not ready. The focused spec now checks removal of a retained
not-ready root; it remains unrun on the source-matched runtime. A live cleanup
failure injection must prove the pending root is eventually removed.

The parent attempt now also preserves a failed cleanup root after intent or
admission rejection, pre-upload revocation, upload failure, digest mismatch,
and post-worker completion. The parallel parent marks local cleanup failure
as requiring reconciliation, so a published result is not reported as a
fully clean run. These branches have static review only in this session; a
source-matched failure-injection test remains required.
The parallel preparation envelope retains the typed cleanup handle when
deletion fails. Its synchronous runner reports the exact root and requires
explicit recovery; durable automatic cleanup is not yet implemented.
