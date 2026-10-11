# Windows ReFS durable file flush stalls bootstrap admission

Status: host-specific reproduced blocker; NTFS diagnostic continuation in progress.
No compiler admission or Phase 4 completion is claimed.

On 2026-10-11 the Windows Stage 2 candidate completed its 1,233-module build,
then stalled during the frontend sanity SCV prime. PID 9144 stopped accumulating
CPU while the bounded collector retained its original 1,800-second deadline.
A noninvasive debugger stack showed `NtFlushBuffersFile` through
`FlushFileBuffers` and candidate offset `+0xe4c04a`. Offline disassembly matches
`src/runtime/runtime_secure_staging.c`'s `rt_file_sync`, including its freshly
opened read/write handle with read-only sharing; this is not stdout flushing.

The handle targeted the approximately 2 MB `SCV_COMPILE_INVENTORY.tmp` below
`D:/dev/simple-windows-phase4/build/scv/snapshots/.tmp.9144.*`. The owner chain is
`compile_snapshot.spl` → `store.spl:scv_write_text` → database `atomic_write`
→ `rt_file_sync`, before atomic rename. The writer has closed before the sync.
Retained evidence is in `build/windows-phase4-logs/stage2-sanity-stack.txt` and
`stage2-sanity-sync-path.txt` in that checkout.

An independent .NET one-byte `FileStream.Flush(true)` probe also hung on the
host's D: ReFS volume (collector session 8103). The same probe on C: NTFS
completed in approximately 10 ms. This isolates a host/storage durability
boundary independently of compiler lowering and SCV inventory size; it does
not establish that all ReFS systems fail or identify the responsible filesystem,
filter, or storage driver. Preserve the original timeout and probe evidence.

Continue diagnostics on a verified copy of the source contents on NTFS, with
separate NTFS output, parse CAS, and temporary directories. Keep the candidate
immutable and preserve the old caches and failed receipts. Do not disable
`FlushFileBuffers`, report a timed-out sanity check as passing, or transplant
path-bound admission receipts. The canonical provisional launcher must first
compile and execute its own Hello and remains diagnostic-only.

The copied manifest differed only in three materialized junctions' absolute
checkout roots; every other record, including all content hashes, matched.
Keep both canonical manifests and the explicit relocation comparison. Different
manifest hashes require fresh lineage rather than admission reuse.

Moving only `--output-root`, `--cache-dir`, or `--shared-parse-cas-root` is
insufficient: provisional Hello and manager builders change into the source
checkout, and `compile_source_inventory_checkout_cache_root_v1` selects
`<checkout>/build/scv`. SCV also validates snapshot ownership there. A source
junction back to D: does not move its storage. Reuse existing caches only where
their source/path/runtime/producer contracts still match; keep rejected caches
for diagnosis rather than rewriting their receipts.
