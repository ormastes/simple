# Cold SCV snapshot materialization lacks a per-file scratch owner

Status: ownership gap in the older local workspace source. The coherent source
cut and remote branch already include a per-file scratch implementation; its
native qualification is pending. Hold the duplicate private repair proposal.
Bug DB writer reconciliation is pending; no database state is claimed.

## Source identity and existing repair

The originally inspected local workspace remains at HEAD
`2fbcf0cf3e01ed48ec3f4952a030fae89858a6e2`; the inspected local owner has SHA-256
`17d43cbc94fea1c4d2d0ffc647563fb43e402f825ce2d31e566513d689b8a7ce`.
That observation must not be presented as a missing implementation on the
remote branch or in a newer compiler binary.

The coherent source cut `cce267e717684e7f87aea1603df3da7c0745258d` and reviewed
remote `release_phase3` revision
`e703d29ccfdd75336a5fc72c83131ebdb2daa3d4` contain
`scv_compile_snapshot_materialize_source_v1` at line 398, called per entry at
line 484. The reviewed remote owner blob is
`b0a7213872bb02e599ec2082157f994c890a3e58`. It imports the canonical
`std.nogc_sync_mut.sffi.transient` surface and performs begin, pause, promotion
and end around the production materialization result.

The existing implementation fails safely when scope acquisition fails, whereas
the duplicate private proposal below retained an unscoped fallback. They are
different policies and must not be silently combined. First qualify the
existing implementation with its real native provider, retained result/error
roots, nested-epoch behavior and identical cold/warm inputs. Source existence
alone does not prove reclamation, performance or inclusion in the admitted f2
binary. Do not add another provider or replace the existing owner merely to
make a private diagnostic compile.

## Original local-source finding

Shared compiler entrypoint admission calls inventory refresh, snapshot acquire,
and source-authority binding validation before native-build dispatch. Current
`src/app/compiler_entrypoint/inventory_scratch.spl:11` already bounds one file's
canonicalization/hash scratch with a transient scope and promotes only its event.
By contrast, `src/lib/scv/compile_snapshot.spl:339-373` materializes all selected
entries without an equivalent per-file ownership boundary.

Each cold iteration reads and hashes the admitted original, publishes or finds
and rereads its content chunk, writes and rereads the destination, then rereads
the original for drift. The checked readers and UTF8 conversion create text and
byte-array payloads. Leaving a function or loop iteration does not establish
reclamation on the no-GC core-C provider. The exact retained byte growth of this
production path has not yet been measured. All four integrity/drift checks have
distinct purposes and must remain intact.

This is a cold materialization finding. The existing warm branch at
`compile_snapshot.spl:299-329` derives the revision from admitted inventory and
authenticates an existing snapshot's metadata/receipt without rereading every
source body. Warm inventory refresh also has an unchanged-cursor fast path.
Remaining inventory and manifest rereads are metadata validation; they must not
be described as unconditional whole-source reads on every entry.

The retained f2 web run took579.903s with11,071,852KiB sampled peak and no binary.
Its inner source phase took2.046s, including a0.505s owner-copy span. Those facts
do not identify the function responsible for the earlier delay. Current source
is not proof of what was embedded in f2. No latency or memory gain is claimed.

The private proposal at
`build/native_probe/scv-materialization-scratch-20261013/` factors the real
materialization iteration and promotes only its manifest-row/error result before
ending an acquired scratch scope. The accumulated manifest remains outside that
scope. Cleanup and failure diagnostics remain at the original staging boundary.
The existing MIR scope wrapper moves behind a canonical no-GC SFFI owner with a
compatibility surface; the runtime policy and ABI are unchanged.

A failed scope acquisition must never pause, promote through, or end an outer
request's epoch. The proposal retains the original unscoped behavior in that
case, including nested and concurrent acquisition failure. It makes no bounded
scratch claim for that fallback. A successfully acquired scope must retain error
text as well as successful rows before cleanup; the escaping result is constructed
after scratch ends. Native text promotion and any I/O/global state retained by
callees remain explicit proof obligations.

Required prevention evidence: actual production cold acquire and complete warm
reuse; valid and corrupt chunk cases; destination/read failures and drift;
retained error/manifest bytes after cleanup; nested outer-epoch survival;
cancellation at actual supported boundaries; a subsequent valid operation after
failure; native allocation observations plus paired cold/warm wall, CPU and RSS
under identical immutable inputs/provider. Registry object counts alone are not
byte accounting. A process terminated at Job0 does not prove in-process cleanup.
No source diagnostic or primitive replay substitutes for this native owner path.
