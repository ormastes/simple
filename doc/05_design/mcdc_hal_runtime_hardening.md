<!-- codex-design -->
# MC/DC and HAL Runtime Hardening Detail Design

## Frozen public types

- `McdcPolicy`, `McdcDecisionId`, `McdcManifestV1`, `McdcDecisionRowV1`, `McdcConditionRowV1`, `McdcObservationV1`, `McdcWitnessV1`, `McdcErrorV1`.
- `HalProviderKind`, `HalRunMode`, `HalAssurance`, `HalSideEffectPolicy`, `HalCapacityV1`, `HalOperationV1`, `HalProviderRequestV1`, `HalProviderResultV1`, `HalStatusV1`.
- `EnvOpcodeV1`, `EnvInstructionV1`, `EnvObservationV1`, `EnvTraceV1`, `ExclusionKindV1`, `ScenarioExclusionV1`.

All safe-boundary wire values use fixed-width scalars and checked `(offset,length)` regions. Dynamic text, dictionaries, closures, runtime values, and growing arrays do not cross the sealed boundary.

## Compilation flow

1. Resolve `McdcPolicy` and migration release once; include both in compilation/cache identity.
2. Interpret generic `@rt(hal, ...)` attributes and compute effective assurance through entry-closure reachability.
3. Build sorted MC/DC and HAL manifests; reject collisions, malformed capacities, lower-assurance reachability, and new/changed migration findings.
4. When policy is not static-off, insert correlated MIR observations and validate dominance/commit completeness.
5. Preserve observations as ordered effects through optimization.
6. Lower through one backend-neutral sink contract.
7. Select static sink or dynamic activation descriptor in the link closure; static-off selects neither.

## MC/DC proof algorithm

Observations deduplicate by decision ID, evaluated mask, masked value mask, and outcome. For each condition, search deterministic pairs in sorted order. Accept unique-cause first. For masking fallback, evaluate the frozen postfix Boolean DAG for all allowed values of changed or unevaluated non-target atoms within the proof budget. If every completion preserves each observation outcome and the target flips the decision, emit a masking witness; otherwise leave uncovered. Proof exhaustion is not an exclusion.

The complete report uses the additive `SimpleMcdcReportV2` ABI. The caller
supplies the independently measured executable SHA-256; the manifest digest
remains a separate identity bound by V1 provenance. Compiler-owned
source locations are supplied as fixed `(file_digest,line,column)` rows in exact
manifest order. Report creation fills fixed decision rows and binds every row
to mode, binary identity, process identity/sequence, masks, and a SHA-256
integrity receipt. Cross-process inputs are sorted once by decision identity
then process provenance; the merge performs one linear scan, unions covered
masks, requires identical eligible/excluded masks and an identical process set
for every decision, and writes only caller-owned output. It allocates no memory
and an empty eligible denominator remains a hard failure.

## Dynamic activation state machine

`Absent -> Validating -> Prepared -> Armed(generation) -> Disarming -> Settled -> Absent`.

Validation checks catalog route, content/index/signature hash, binary/manifest/ABI identity, capacities, relocations, and advice chain. Preparation supplies/maps all storage before the critical boundary. Batch slot updates publish one generation with release stores; readers acquire. Failure before publication has no visible effect. Failure during disarm leaves the pack mapped but disarmed and emits a bounded failure receipt.

## Provider state machine

`Created -> Initialized -> Sealed -> Running(invocation) -> ReceiptReady -> Validated -> Compared -> Committed|Rejected -> Idle -> Shutdown`.

Workers are preinitialized before `Sealed`; there is no per-operation spawn. The parent drains all bounded result pipes fairly to avoid pipe deadlock, applies one deadline, cancels and reaps every child, validates complete consumption, sorts receipts, then normalizes/compares. Parent commit is a single transition and records the selected provider/plan plus every compared receipt hash.

The landed native session owner is `hal_provider_sealed_session_v1`. It owns
exactly three fixed Pure/C/Rust lane records and 512-byte input/output arrays.
`prepare` starts the trusted launchers and waits for their sandboxed workers'
readiness receipts; `seal` rechecks liveness; `enter_critical` closes the
maintenance boundary. Each invocation broadcasts a generation/sequence/reset
frame, validates all reset acknowledgements, then broadcasts one bounded
request and retains results in provider-ordinal slots. No allocator or process
creation symbol occurs on that path. A timeout or protocol failure makes the
lane unhealthy and fails the whole invocation without committing partial
sequence state. Kill, reap, and restart are permitted only after
`leave_critical`, which also unseals the session. The session is a sole-parent
owner and is not a multi-writer object.

## Environment plan and replay

The extractor writes strictly increasing instructions into a caller buffer and seals a digest. The executor validates capability, safety policy, capacity, and sequence before applying any instruction. Plan-Then-Commit performs the accepted plan once; ReplayOnly feeds recorded observations to shadow providers. A provider requesting an unrecorded or different interaction returns `InvalidRequest`/`Diverged`, never ambiently performs it.

`RtHalEnvironmentBindingV1` is the parent-owned bridge from a manifest-pinned
numeric operation identity to that extractor. Operation 101 is the production
`io.clock.monotonic_nanos.v1` declaration, operation 102 is environment lookup,
and the remaining typed adapters use `1000 + EnvOpcodeV1`. The binding retains
only fixed scalars and the existing extraction cursor. Extraction is O(1) per
interaction with no lookup, hashing, collection, or allocation; replay performs
only the unavoidable O(result bytes) copy into caller-owned storage. A cursor
preflight occurs before that copy, so a duplicate or reordered replay cannot
mutate the result region, reread ambient state, or consume twice.
The additive provider-result V2 trace position mixes the operation and schema
identities into the sealed plan digest and carries the exact consumed cursor;
cross-operation relabeling and incomplete provider consumption therefore fail
comparison without retaining a dynamic transcript.

### Ambient environment and clock capture

`HostedPreparedEnvironmentGetExecutorV1` performs its single ambient lookup
before seal, rejects non-byte text and keys or values above 64 KiB, and pins the
exact key plus capability. `HostedPreparedClockReadExecutorV1` similarly
captures one eight-byte timestamp before seal and pins its capability. Neither
sealed executor retains a host-access callback.

The canonical parent creates a value-semantic cursor bound to one positive
invocation identity. Execution admits only sequence zero, the exact opcode,
capability, argument bytes, and caller-owned result capacity. It copies the
prepared bytes into the caller region, returns a consumed cursor, and reports
zero allocations after seal. Reusing the consumed cursor, presenting a stale
cursor copy to the parent, or changing invocation/capability/bytes/capacity
fails before result mutation. The parent is the sole cursor commit authority;
provider copies are candidates only.

Exact replay consumes the recorded observation and caller-owned recorded bytes,
marks `physical_effect=false`, and never calls the environment or clock facade.
Thus capture performs at most one host interaction, canonical consumption occurs
at most once, and any number of isolated comparisons can replay without host
effects or dynamic storage growth.

### Hosted bounded file write adapter

`HostedPreparedFileWriteExecutorV1` admits one existing regular file beneath a
trusted root before seal and pins its path as two scalar digest lanes. The
canonical parent owns a value-semantic `HostedFileWriteCursorV1`; only its
unconsumed state may commit sequence zero, and the returned consumed cursor is
authoritative. The payload must be the complete caller-owned argument region,
bounded to 64 KiB, so the commit path passes it directly to the canonical
`app.io.file_write_bytes` facade without slicing, copying, formatting, or
growing storage. The 17-byte caller-owned result binds success and both path
digest lanes into the ordinary interaction receipt. The adapter rechecks the
regular-file predicate around the write and verifies the final byte length.
Replay uses `env_replay_exact_v1`, copies only the recorded 17-byte result, and
performs no filesystem operation. Duplicate canonical-cursor consumption,
changed capability/sequence, nonzero payload offsets, oversized payloads,
replacement, short writes, and insufficient result storage fail closed.

The parent is the sole cursor owner: stale cursor copies are invalid transport
and must never be committed by an isolated provider. Preparation may allocate
path metadata before the critical boundary; the execute and replay loops use
only caller-owned buffers and fixed scalar state and report zero post-seal
allocations. This hosted pathname adapter assumes a trusted fixture directory;
hostile shared directories require a future descriptor-relative no-follow
facade rather than weakening this contract.

### Hosted file-read lifecycle and stream-write adapters

`HostedPreparedFileReadSessionV1` closes the executable `FileOpen`/`FileClose`
gap around a bounded read. Preparation admits and captures one stable regular
file beneath the trusted fixture root, then retains fixed digest lanes, a
derived nonzero handle token, capability identity, and at most 64 KiB of
captured bytes. The canonical cursor admits exactly `FileOpen -> FileRead ->
FileClose`. Open binds the caller-provided path digest, read binds the returned
handle, and close consumes it. Changed identity, opcode, sequence, capability,
capacity, or cursor state fails before modifying result storage. Canonical
execution copies into caller storage without growth and reports zero post-seal
allocations; exact replay never rereads or closes a host resource.

`HostedPreparedStreamWriteExecutorV1` binds a nonnegative stream identity and a
caller-owned sink fixed before seal. One `StreamWrite` carries the identity as
an eight-byte prefix followed by at most 64 KiB of payload. Execution copies
the payload directly into the admitted sink and returns the written length in
the caller's eight-byte result region. Its consumed cursor rejects duplicate
writes. Replay copies only the fixed result receipt, so it cannot mutate the
sink. This is the deterministic environment-model adapter; a concrete pipe,
terminal, or device owner may commit the accepted caller buffer outside shadow
provider execution.

### Hosted bounded process lifecycle adapter

`HostedPreparedProcessExecutorV1` creates one allowlisted composition-owned
process before seal, after bounding the command to 1024 bytes, at most 32
arguments, and 8192 aggregate bytes. It discards command storage at the sealed
boundary and retains only the PID, capability, and two command-digest lanes.
`HostedProcessCursorV1` is the canonical value-semantic parent cursor. It admits
exactly `ProcessSpawn(sequence=0)`, followed by zero or more ordered polls and a
single terminal kill. Spawn admission must present the exact 16-byte command
digest and returns the pinned PID; poll and kill must present that PID. Changed
capability, identity, sequence, opcode, capacity, or a stale/terminated cursor
fails closed before an effect.

The lifecycle hot path calls only scalar process liveness/kill facades and
writes fixed 8-byte or 1-byte results into caller storage. It creates no array,
text, process, or result object with variable capacity after seal and reports
zero post-seal allocations. Process construction remains preparation work,
which is necessary because a real spawn can allocate in the host runtime.
Replay uses `env_replay_exact_v1`; therefore a recorded kill or poll copies its
fixed result and never consults or changes the host process. The parent must
retain and commit only each returned cursor; isolated provider copies cannot
advance or repeat the canonical lifecycle.

### IRQ/MMIO/DMA environment adapter

Producible hardware scenarios use `DeviceSandboxExecutorV1`; it is a software
model and never maps `/dev/mem`, installs a host interrupt, pins host pages, or
submits host DMA. The parent owns the model, argument, result, and replay byte
regions. The sealed executor retains only scalar capability/lifecycle state.
Its hot method performs bounded byte copies and reports zero post-seal
allocations; no buffer is created or resized there.

Every instruction carries a generation-bound `DeviceCapabilityProofV1` and the
exact digest of one sealed `DeviceRangeGrantV1`. The environment composition
owner supplies a separately pinned authority digest, minimum generation, and
device identity; an instruction or provider cannot supply or replace that pin.
Admission checks the opcode mask, proof lifetime, pinned authority, capability
identity, grant digest, non-wrapping range,
MMIO width/alignment and permissions, IRQ allowlist, DMA alignment and the
64-KiB transfer ceiling before changing any caller buffer. Side-effecting MMIO
writes require an explicit side-effect flag. Side-effecting reads and interrupt
acknowledgements require a 1..62 read-once token; duplicate consumption fails
as `Diverged`. DMA submit/poll additionally require explicit direction flags
and an admitted map lifecycle. Map retains the exact address and length;
submit/poll must remain inside it and unmap must name it exactly.
Interrupt acknowledgement additionally requires a fixture-owned pending bit and
a preceding mask transition. Its 1..62 token is bound to the granted IRQ by a
bounded modulo partition and is consumed globally, permitting multiple planned
events without an unbounded token table.

Replay revalidates the proof and grant against the same pinned authority and
device identity, compares every device-specific scalar including address,
width, IRQ, token, generation, and grant digest, then delegates to the canonical
exact byte/digest replay. It never consults or changes the model. Hardware that
cannot be safely produced may be removed from the eligible denominator only
through one of the five governed REQ-018 kinds, with its exact registered
predicate, `producible=false`, fresh observation evidence, and 8..256 printable,
nonblank reason bytes plus owner/review/expiry proof. It is reported as excluded,
never executed or counted as covered.

The applied receipt carries a second two-lane digest over the pinned authority
and device identity, proof generation/lifetime/opcode mask, full grant policy,
device instruction scalars, and canonical environment observation. Replay
recomputes it, so replacing both caller-supplied instruction objects cannot
reuse a receipt for another address or device. The public scalar constructors
are composition/test vocabulary, not a host authority mint: production pins
must originate in the trusted environment owner. Even a forged private model
never gains a host-device effect through this adapter.

## Fixed-capacity behavior

Every manifest declares required frame depth, event words, trace operations/bytes, request/result bytes, diff rows, deadlines, and log bytes. Initialization either supplies them completely or fails. At exact capacity, the final valid record succeeds. Capacity+1 sets sticky overflow with kind, first sequence, and count; no diagnostic allocation occurs. The combined default event/log capacity is <=4 MiB and may be configured downward.

## Migration verifier

The verifier uses compiler-resolved declarations and entry closures. Its baseline fingerprint is `(rule_id, canonical_module, symbol, source_span, normalized_signature)`. Candidate recording never modifies the accepted baseline. Receipt status passes only when new/changed/stale/malformed/expired counts are zero and every pre-milestone warning exactly matches the baseline; at/after milestone total findings and baseline entries must both be zero.

The bounded source migration scan also treats every `@rt(hal)` and `@noalloc`
body as a zero-growth closure. It recognizes raw heap entry points and hidden
growth through `push`, `append`, `insert`, and `reserve`; comments are ignored.
Allocation is admitted only when the same declaration is explicitly on the
`@init_phase` side of the startup seal. This is a migration aid, while the
compiler semantic no-allocation closure remains authoritative. Findings in
new or changed files are immediate errors, exact untouched baseline findings
are warnings, and the configured enforcement epoch promotes every remaining
finding and baseline row to an error.

The scan runs only during build/verification and is absent from HAL runtime
closures. It inventories files once, reads each admitted file once, and uses
bounded file/byte/finding limits; the policy evaluator uses indexed sets and
is linear in findings, baseline rows, and changed paths. Its receipt reports
scan microseconds, source bytes, file reads, and inventory process count;
the companion performance runner reports wall time and peak RSS. No new
runtime allocation, branch, table, or logging surface is introduced by this
guard.

## Error handling

All APIs return `Result<T, E>` or closed status values. Unknown dispatch arms, schema versions, providers, opcodes, comparators, normalizers, predicates, and receipt fields are catchable failures. No abort/unreachable fallback is permitted. Overflow, timeout, child crash, malformed receipt, pack failure, stale exclusion, and allocation violation preserve actionable bounded provenance.

### Governed scenario exclusion expression

An environment scenario that cannot be physically produced may use exactly one
compiler-verifier directive:

```text
# @mcdc-exclude: scenario=<stable-id> | decision=u64:<16-lower-hex> | source=u64:<16-lower-hex> | conditions=u64:<16-lower-hex> | condition-count=<1..63> | kind=<governed-kind> | code=<stable-id> | capability=<stable-id> | predicate=<registered-kind-predicate> | producible=false | reason=<8..256 ASCII bytes> | evidence=sha256:<64 lowercase hex> | observed=<unix-seconds> | owner=<stable-id> | reviewed=<unix-seconds> | expires=<unix-seconds>
```

The five registered predicates are `capability.unavailable`,
`fixture.unavailable`, `platform.inapplicable`, `safety.prohibited`, and
`nondeterminism.uncontrollable`, paired in that order with the five kinds. An
unknown kind, predicate mismatch, or `producible=true` fails closed. This is not
a generic skip. The predicate observation must precede review and remain fresh
at verification time. The line is bounded to 1024 bytes, identifiers to 96
bytes, and both observation and review lifetimes to 90 days. One linear compiler audit accepts
at most 256 directives from a source of at most 4 MiB, retains only the bounded
stable-ID hash index needed to reject duplicates, and performs no runtime/hot-path work.
The scanner walks source offsets rather than splitting the full source into a
line array: it copies at most one 1024-byte candidate line at a time and retains
at most 256 identifiers of at most 96 bytes each. Parsing a candidate has a
fixed 16-field binding shape. The legacy 11-field spelling remains parseable
for diagnostics but cannot pass the binary binding gate. Thus auxiliary storage is bounded independently of source
line count; the offline verifier may allocate within those caps, while runtime
probe paths allocate nothing for exclusion governance.
The verifier reports an accepted
entry as `EXCLUDED`, never `PASS` or covered. Stable decision/exclusion joining
owns denominator removal; the directive audit is an additional normal-mode
gate. Before that gate, one ordered O(N) pass compares each directive with the
corresponding 376-byte row: decision/source/mask/count, five-kind predicate,
FNV-1a-64 scenario/code/capability/owner identities, the first 128 SHA-256
evidence bits, epochs, exact ASCII reason bytes, and zero padding. Missing,
extra, duplicate, reordered, or tampered rows fail closed; a validated report
count alone is insufficient. A blank or placeholder reason, malformed identity, missing SHA-256
evidence, future/stale observation, future review, expired entry, or overlong
review window is an error.
Consequently, exclusions reduce only the eligible denominator and never increase
the covered numerator.

## Performance implementation notes

- Per-thread fixed shards; one compact commit per decision evaluation.
- Static tables sorted once; no hot-path registry construction.
- Dense runtime slots with stable semantic IDs retained in manifests/receipts.
- No locks, dictionaries, formatting, I/O, env reads, timestamps, or loader calls in probe paths.
- Persistent isolated workers amortize startup; isolation setup costs remain separately reported.
- Offline rendering turns binary receipts into intensive human logs.

The focused native evidence compiles the owner under ASan/UBSan, performs 1,000
sealed three-provider invocations, asserts zero hot spawn/allocation counters,
caps the owner at 4 KiB, and rejects allocator imports in its object file. Host
latency is retained as a measured value, not a portable threshold. Live
bubblewrap execution remains fail-closed on hosts where user namespaces are
unavailable; such a host result is not isolation evidence.

## Compatibility

Existing `std.mcdc` analysis APIs become a facade over the canonical model. Global registration/growing evaluation APIs and Boolean `coverage` config warn only for exact untouched legacy fingerprints. Existing I/O APIs delegate to tagged operations during the migration; raw aliases and app-owned HAL paths are forbidden.
