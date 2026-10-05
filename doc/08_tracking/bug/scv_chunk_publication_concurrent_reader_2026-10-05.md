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
