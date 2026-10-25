# Snapshot reopen validation has no bounded scratch lifetime

Status: source repair and seven real regression scenarios authored, UNRUN.
Memory reduction, performance and runtime correctness remain unverified.

The original Phase3 attempt hit its aggregate RSS guard before object output.
A separate user-authorized diagnostic disabled only RSS enforcement, retained
monitoring and the 1800-second timeout, then exited 124 at timeout with peak
RSS 7,058,684 KiB and no candidate. Raising the guard did not resolve the
long-running compilation. This repair is independent of that diagnostic.

The snapshot reopen owner reads the complete inventory, hashes its bytes,
splits all rows and three fields per row, checks paths/count/provenance and
receipt, then returns only a compact `ScvCompileSnapshotV1`. Without a scratch
owner those temporary managed allocations can remain until process exit.
The coordinator waits for its compiler worker, so that lifetime spans worker
compilation. The actual observed manifest is 2,293,062 bytes and 18,568 rows,
with maximum row length 195 characters and 376 bytes of provenance.

Those sizes support a bounded metadata-retention repair. They do not explain
the entire coordinator heap, worker growth, timeout or 7 GiB aggregate peak.
At core-C's 16-byte string header and 32-byte array header plus 8-byte slots,
the main row/field copies, manifest and hash input are on the order of tens
of MiB. This is a structural estimate, not an RSS bound or measured saving;
allocator overhead and other owners require independent profiling.

`scv_compile_snapshot_open_v1` now owns scratch only for reopen validation.
It is intended to promote the compact returned authority graph and retire
temporary buffers before returning. Its unchanged unscoped implementation
retains every original validation. An existing active/paused caller scope
remains caller-owned; an unsuccessful begin preserves existing behavior.
No wrapper surrounds complete snapshot acquisition or materialization, whose
per-file scratch owners remain separate. Cache keys and admission checks are
unchanged. No Any diagnostic or memory gate is disabled by this source patch.

The pinned `std.nogc_sync_mut.sffi.transient` promotion wrapper uses a `mut`
generic root so promotion sees the caller's exact value struct. This is
required by the previously documented defensive struct-copy defect.
Reopen validation uses path/metadata/file and hash operations. The metadata
adapter has a lazy process-global platform array. The wrapper primes that
cache before beginning owned scratch, while allocations are persistent;
otherwise a cold open could leave the global pointing at retired storage.
Independent review caught this hazard because fixture writes normally prime
the cache and would hide it. The path-absolute facade delegates to the selected
runtime. Row validation, owner derivation and hash buffers are local. Runtime
literal/short-string caches use persistent allocation; no scope-owned manifest
row is published to a global library memo.

Regression source:
`test/01_unit/compiler/driver/compile_snapshot_open_scratch_spec.spl`.
It authenticates actual metadata and verifies every returned authority field
after allocation churn; rejects changed manifest bytes, a hash-valid unsafe
row and a changed receipt; resets the platform cache immediately before open
and checks later adapter reads after retirement/churn; and verifies both
active and paused caller scopes remain caller-owned. All seven scenarios
await a qualified self-hosted runtime.

Admission requires actual regression execution, comparable before/after
per-process memory and time measurements on identical snapshot inputs, then
the normal memory gate for the original full target. This patch alone does
not qualify Phase3 or fix unprofiled worker memory growth.
