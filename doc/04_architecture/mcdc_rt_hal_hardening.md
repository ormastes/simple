<!-- codex-design -->
# MC/DC, RT, and HAL Hardening Architecture

## Decision

Use an MDSOC virtual capsule, `McdcCoverageCapsule`, with compile-time transforms
for static off/on and a runtime adapter only for dynamic aspects. Pure Simple owns
semantics and policy. C/Rust remain delegated storage/patchpoint or comparator
adapters at existing boundaries.

## Layers and authorities

1. `compiler/00.common/coverage` owns frozen modes, IDs, metadata, diagnostics.
2. Frontend owns syntax and exact source occurrences; HIR/semantics owns decision
   graphs, masking/coupling, exclusions, RT policy and effect admission.
3. MIR preserves short-circuit CFG and emits begin/condition/end probes only after
   actual evaluation. Static-off removes all probes/metadata before optimization.
4. Backends lower common probes. Dynamic-capable targets emit dormant patchpoints;
   unsupported targets reject or explicitly declare an inert branch fallback.
5. Driver is the sole configuration/severity/cache-identity authority. Leaves do
   not read environment state.
6. `lib/common/mcdc` owns portable frozen records. `nogc_sync_mut/mcdc` owns fixed
   per-execution-owner recording and bounded analysis.
7. `lib/common/rt_hal` owns provider/request/result/effect contracts. Pure Simple
   is mandatory execution authority; comparator workers return child-created
   results for deterministic parent validation/commit.
8. The canonical app host facade is sole `EnvAccessInstruction` executor and
   returns `EnvAccessReceipt`; test leaves are effect-free.

Sibling layers exchange frozen common records/ports only. Recorder owners possess
canonical mutable rings; the report builder owns aggregation; the environment
executor owns host effects; the driver owns policy. Boundary data is frozen share
for requests/metadata, encoded payload for process/provider transport, child-owned
result on return, and parent-authoritative deterministic commit. No raw pointer or
unknown dynamic payload crosses a safe external boundary.

## MC/DC hot path and analysis

Stable identity is module-qualified source identity plus decision ordinal and
condition occurrence. An evaluation stores decision/owner/sequence, outcome,
evaluated mask and true mask. Untouched bits mean NotEvaluated. A fixed nesting
stack aborts throwing evaluations without inventing an outcome.

Each owner uses a preallocated power-of-two SPSC ring (default 1 MiB; global cap
default 64 MiB). A record write is O(1): no heap, names, formatting, I/O, global
lock, loader lookup, or provider dispatch. Overflow is explicit drop-newest or
overwrite-oldest; normal+ treats saturation as incomplete evidence.

The analyzer builds bounded per-condition signature buckets while ingesting E
evaluations. It retains the lexicographically earliest validated opposite outcome,
giving expected O(E*C) time without pairwise O(E-squared) search. Exact integer
covered/required equality alone means 100%.

## Dynamic activation

Activation validates ABI/schema/capacity, then publishes a generation only at a
quiescent barrier outside active RT regions. Patchable targets switch an inert
NOP/static key; other admitted targets may use one predicted disabled branch and
must report that cost. Static-on uses direct lowering, never dynamic dispatch.

## HAL and environment effects

Read-only HAL queries may run in bounded workers over frozen requests. Results
commit by configured provider ordinal and case ID. Effectful work executes exactly
once through Pure Simple; comparators receive only canonical trace/replay and lack
effect capability. Unsupported, timeout, mismatch, and blocked are distinct.

Environment plans contain typed instructions, declared tools, time/output/process
budgets, and no arbitrary command. The executor streams into bounded capture,
hashes discarded excess, and returns a typed status and resumption evidence.

## RT admission and migration

Canonical tier is `critical`; `mission-critical` remains an alias. New RT
declarations default critical. Existing implicit declarations emit stable
`W-RT-PROFILE-001` for one edition/profile epoch; the next epoch maps the identical
rule/span/fix to `E-RT-PROFILE-001`. Explicit lower tiers remain visible and need a
reason in normal+.

Post-monomorphization transitive summaries must prove bounds for allocation,
blocking, loops, recursion, dispatch, synchronization, logging, and loader work.
Unknown fails closed. Accepted hot paths gain no runtime checks.

## Stable failure families

`MCDC-E-MISSING-PAIR`, `MCDC-E-EXCLUSION-*`, `MCDC-E-BUFFER-SATURATED`,
`MCDC-E-DYNAMIC-UNSUPPORTED`, `MCDC-E-PROBE-UNLOWERED`, `RTHAL-E-MISMATCH`,
`RTHAL-E-UNSAFE-REPLAY`, `RTHAL-W-UNSUPPORTED`, `ENV-E-UNDECLARED`,
`ENV-B-BLOCKED`, `RT-{W,E}-IMPLICIT-CRITICAL`, and category-specific
`RT-E-UNBOUNDED-*`. Machine and human forms derive from one typed record.

## Migration

Freeze contracts/diagnostics and baseline; land static native MC/DC and parity;
prove static-off elimination; land bounded recording/analyzer/exclusions; land
environment receipts; add Pure-first HAL query and execute-once comparison; add
dynamic target adapters; run the RT warning epoch; promote to error next epoch;
retire the rewrite only after compatibility and parity evidence.
