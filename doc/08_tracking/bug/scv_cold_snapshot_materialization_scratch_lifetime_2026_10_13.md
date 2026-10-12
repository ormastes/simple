# Cold SCV snapshot materialization lacks a per-file scratch owner

Status: current-source ownership gap; private repair proposal UNRUN. Native
growth, reclamation and performance qualification are pending. Bug DB writer
reconciliation is pending; no database state is claimed.

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
