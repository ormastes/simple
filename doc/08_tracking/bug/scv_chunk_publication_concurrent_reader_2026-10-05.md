# SCV chunk publication exposes an unfinished final path

Status: OPEN; source-level publication race identified, incident causality not yet reproduced deterministically.

## Observed failure

The Cranelift `native_shared_io_type_provenance` probe, source
`e37658577b3279e30f1631dfcc8474d1c860511b`, compiled by Phase 2 producer
`2b83155910336e56ec8b663c3d3e7d3ceb9c61b60fa98182163f9670ff044c33`,
exited 1 before MIR with:

`SCV-E-ADMISSION: snapshot-chunk-publish-failed:src/os/kernel/arch/arm32/cosmos/cosmos_storage_policy.spl`

Evidence: Windows restart packet
`qualification-helper-e37658-cranelift1/cranelift/native_shared_io_type_provenance/compile.log`,
SHA-256 `403d97d441a3fc61f23c9f464592584c18d22e04547645ce5c06dae5fcf9849f`.
Elapsed compilation 1031.615 seconds; no executable or test execution.
An overlapping LLVM probe used the same immutable source and chunk store.

After failure, the source and final chunk both contained 3798 bytes with SHA-256
`057dc2471951fb67992127af68129e400fef91c068e487b41e6a77a3f4e37ece`.
This is consistent with a publication race, but does not independently prove
which system call failed during the original incident. Free disk space at
inspection exceeded 115 GB.

## Source-level defect

`src/lib/scv/compile_snapshot.spl::scv_compile_snapshot_write_chunk_v1`
creates the digest-named final path with `file_create_excl` and only then checks
its digest. Another process that sees that path immediately tries to read it.
`src/runtime/runtime_secure_staging.c::rt_file_create_excl` uses Windows
`CREATE_NEW` with sharing disabled, writes bytes, then closes the handle.
The name therefore exists while it is unreadable; on POSIX it can be readable
before all bytes have been written. Exclusive creation does not provide atomic
publication of complete content.

## Required repair and verification

Stage and verify bytes in a private path, then publish with the existing
no-replace publication primitive. A losing publisher must validate the complete
winner. Preserve rejection of corrupt existing chunks, immutable cache identity,
and cleanup of private staging files. Do not overwrite or delete active caches.

Add a deterministic overlapping-writer/reader regression, a corrupt-existing
chunk case, and failure cleanup coverage. Measure warm and cold latency plus
peak memory: avoid introducing one extra temporary directory or unbounded retry
loop per source file. Native verification remains pending. This bug is separate
from the typed probe's unsupported Result payload lowering failure.

## Isolated repair prepared

`scv_compile_snapshot_acquire_v1` now creates its existing per-snapshot staging
directory through `secure_temp_dir_raw`, retaining the PID recovery field. There
is no per-chunk directory, time-only name, shared mutable nonce, or retry loop.
The chunk writer exclusively creates a file inside that private directory,
verifies its bounded content digest, and calls `file_publish_noreplace_raw`.
The commit helper validates an existing winner on a lost race and never replaces
or deletes that winner. Private stages are removed after commit/failure; failed
exclusive writes remain owned by the enclosing snapshot cleanup, which also
handles partial writes. An existing private-path collision is not deleted by
the chunk helper. The final-path alias guard protects against an invalid helper
call deleting an existing object.

Successful cold publication moves the existing digest verification from the
final path to the completed private file: one bounded source read/hash remains.
A losing publisher additionally validates the winning object. Warm hits keep
the existing final read/hash path and do not allocate a staging directory. The
extra operations on a cold chunk are atomic publication and private-path
cleanup, not another full-content buffer or directory creation. Actual latency
and RSS savings or regressions have **not** been measured.

`test/04_smoke/native_scv_chunk_publication.spl` exercises deterministic
interleavings at the real commit boundary (private prefix, second writer commit,
reader check, first writer completion), corrupt private and existing content,
missing-parent publication failure, collision preservation, warm reuse, UTF-8
and CRLF bytes, and cleanup. It also reports cold/warm timing for sixteen chunks;
the external native owner must record peak process-tree RSS. This is a controlled
interleaving, not a claim that the original concurrent incident was reproduced.
All new native assertions and timing/RSS measurements remain **UNRUN**.

Verification must compile this fixture with a pinned current producer against
an authenticated derived source, then execute it under the existing owned
collector on both backends. Retain exact stdout checks/failure counts, wall time,
RSS and closure receipts. The prior compile-snapshot reclamation regression
remains relevant because per-file transient scope still owns staged hash buffers.
No running source snapshot, build request, or cache was modified by this repair.
