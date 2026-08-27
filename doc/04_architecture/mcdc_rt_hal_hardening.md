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

## Implemented source topology (unverified)

The implementation refines the original three abstract probes into frozen HIR
decision metadata and MIR `DecisionProbe`/`ConditionProbe` records. The MIR
records are compiler-internal markers: `driver_pipeline_lowering.spl` must
expand them to direct static or dynamic runtime calls before backend selection.
Every backend and the MIR interpreter rejects an unexpanded marker. This makes
static-off a compile-time absence property instead of a runtime flag check and
prevents a backend from silently dropping coverage semantics.

Short-circuit lowering records a condition only after its expression evaluates.
It emits explicit evaluated/truth words and Boolean-derivative mask ranges for
the unevaluated side of `and`/`or`. Analysis consumes a per-condition policy:
unique-cause requires equality of all non-target evaluated values, while masking
uses compiler-produced projection words. Missing masking metadata is a named
classification, never inferred from coincidental outcomes. Decision grouping,
policy lookup, and signature matching use bounded open-addressed tables; the
event and signature layouts use inline scalar words rather than per-row arrays.

`dynamic_probe.spl` is the runtime controller. Catalog readiness, ABI/schema
validation, owner registration, allocation, activation, and unload are cold
operations performed only while all registered owners are quiescent. The
published state and TLS owner slot are then sufficient for the dormant probe
path; it does not query the aspect catalog, allocate, format, lock globally, or
perform loader work. Static mode calls the same owner-local capsule operations
directly. Capacity is reserved per owner under the global byte ceiling, and
drop/overwrite saturation remains explicit evidence loss.

## Evidence transport and enforcement

Instrumented test children emit one bounded `MCDC-EVIDENCE-v1` frame. The parent
runner parses only admitted row shapes under byte/row caps, associates them with
the compile-time obligation manifest, runs the analyzer, and feeds one typed
gate report to both machine and human renderers. Normal and stricter assurance
require integer equality of covered and required conditions. Saturation,
malformed transport, missing obligations, invalid exclusions, and missing pairs
fail closed. Reasoned scenario omissions are governed separately from decision
exclusions so an unavailable environment cannot become covered evidence.

## Exact RT/HAL comparison boundary

The current RT/HAL boundary is `rt_hal_compare_observed_pure_exact`. Pure Simple
executes first and supplies the canonical receipt (status, result/error, and
four-word SHA-256 trace identity). A bounded process task arena submits C/Rust
comparison or replay work using frozen scalar arguments, pinned tool identity,
schema, deadline, and output caps. Children return result envelopes; only the
parent compares and commits in case/provider order. Effectful foreign providers
receive the already-observed Pure receipt and replay capability, not authority
to repeat the host effect. Unsupported, timeout, cancellation failure, mismatch,
and memory-bound admission are distinct results.

The public tag facade exposes this production route as
`rt_hal_execute_registered_exact`. It requires at least one configured foreign
comparator and delegates only to installed, isolated process adapters. The
legacy callback-shaped facade remains available for synchronous Pure-only
compatibility, but rejects foreign execution before materializing or invoking a
foreign callback because that shape cannot prove cancellation, frozen input, or
an already-observed Pure receipt.

## Environment, RT criticality, and unwind

`EnvAccessPlan` is validated before the app host resolves a repo-contained path
or a pinned allowlisted tool. The common executor performs a single declared,
bounded instruction through `EnvAccessCapability` and hashes/truncates output
into a typed receipt. Test leaves therefore describe interactions but cannot
open files, read raw environment state, or spawn arbitrary processes.

The source-realized environment vocabulary is a closed 24-kind set. The app
host directly owns bounded environment, identity, repository, admitted-tool,
and clock observations. Socket, device, MMIO, IRQ, and DMA instructions resolve
only through the parent's immutable `(kind, resource, schema, bounds)` adapter
set supplied with that plan; there is no ambient physical-adapter registry.
Adapters retain all mutable handles; instructions and receipts contain no host
pointer or descriptor. Execution stays sequential and parent-authoritative.
Missing or unavailable physical authority produces a canonical actionable
`Unsupported` receipt rather than falling through to a test double.

RT profile/reason/bounds metadata is retained from declaration parsing through
HIR semantic admission. The closure checker computes stable facts and requires
explicit bound capabilities for otherwise forbidden allocation, blocking,
recursion, dynamic dispatch, synchronization, logging, and loader work. Implicit
RT remains a staged critical warning/error controlled by the migration epoch;
no runtime guard is added to admitted hot paths.

Recoverable exceptions use a bounded thread-local runtime frame stack carrying
an integer payload and structural type tag. POSIX ELF x86-64, AArch64, and RV64
native/LLVM paths have source lowering to push/capture/pop and throw/resume.
Unsupported targets fail before emission. C translation, LLVM-library emission,
RV32 payload transport, and composite collision-free type identity remain open
and are tracked explicitly; this architecture is not yet verified end to end.

## Verification status

All topology described above is present in the working source but unverified.
The self-hosted Stage 3/4 runtime is unavailable, no system/performance suite is
accepted, and no static-off binary inventory or timing/RSS/allocation comparison
has been produced. Generated manuals are review artifacts, not execution proof.

## Remediation refinements (unverified)

Masking acceptance is proof-bound rather than based on raw masked bits. The
frontend walks the canonical short-circuit Boolean tree, assigns each leaf a
target context, and records sibling subtrees that must equal the operator's
identity value for that target to control the decision. Tree, proof, and context
fingerprints bind the manifest to that structure; repeated leaf fingerprints
mark strong coupling. The runner derives three-valued context evidence only
after execution and memoizes each sibling program once per row, retaining an
expected O(E*C) cold-analysis shape. A serialized target context is capped at
64 requirements; the decision/event representation remains capped at 256
conditions. Missing, conflicting, or over-cap context evidence fails closed.

The tagged RT return path does not hash, allocate, spawn, wait, format, or
compare. It writes operation, provider flags, Pure scalar receipt, and optional
four-word trace into fixed SoA storage: 16 collision-checked owner slots and 64
receipts per owner (1024 total). After producer quiescence, the controller drains
the ring, constructs exact digests, and performs bounded foreign work. The
injected finalizer makes undrained data, capacity loss, mismatch, timeout, or
cancellation failure a run failure rather than best-effort telemetry.

Hardware interaction is a startup registry of typed app-host function ports,
not executable commands. At most 64 adapters may register before first plan
execution seals the registry. Identity, schema, argument count, deadline, and
output caps must fit the admitted plan; platform absence returns a typed
`Unsupported` receipt. Hardware adapters never receive process-spawn authority.

Real test-only C and Rust executables implement the fixed `rthal-scalar-v1`
protocol. A typed plan invokes pinned compiler paths, hashes each output, and
admits those exact binaries to the arena. Children consume already-observed Pure
receipts and emit bounded outcome/error/trace digests; replay cannot repeat the
host effect.

Recoverable unwind remains asymmetric: POSIX ELF x86-64, AArch64, and RV64 have
native/textual-LLVM source lowering over the bounded frame ABI. C translation,
LLVM-library emission, Mach-O, RV32, and unlisted targets reject with stable
diagnostics. This matrix remains unverified pending cross-backend execution.
