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
exact byte/digest replay. It never consults or changes the model. Hardware that cannot
be safely produced may be removed from the eligible denominator only through a
fresh `CapabilityUnavailable` exclusion with 8..256 printable, nonblank reason
bytes and the existing evidence/owner/review/expiry proof. It is reported as
excluded, never executed or counted as covered.

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

## Error handling

All APIs return `Result<T, E>` or closed status values. Unknown dispatch arms, schema versions, providers, opcodes, comparators, normalizers, predicates, and receipt fields are catchable failures. No abort/unreachable fallback is permitted. Overflow, timeout, child crash, malformed receipt, pack failure, stale exclusion, and allocation violation preserve actionable bounded provenance.

### Governed scenario exclusion expression

An environment scenario that cannot be physically produced may use exactly one
compiler-verifier directive:

```text
# @mcdc-exclude: scenario=<stable-id> | capability=<stable-id> | reason=<8..256 byte reason> | evidence=sha256:<64 lowercase hex> | owner=<stable-id> | reviewed=<unix-seconds> | expires=<unix-seconds>
```

This expression means only `CapabilityUnavailable`; it is not a generic skip,
fixture waiver, or platform filter. The line is bounded to 768 bytes, identifiers
to 96 bytes, and review lifetime to 90 days. One linear compiler audit accepts
at most 256 directives from a source of at most 4 MiB, retains only the bounded
stable-ID set needed to reject duplicates, and performs no runtime/hot-path work.
The verifier reports an accepted
entry as `EXCLUDED`, never `PASS` or covered. Stable decision/exclusion joining
owns denominator removal; the directive audit is an additional normal-mode
gate. A blank or placeholder reason, malformed identity, missing SHA-256
evidence, future review, expired entry, or overlong review window is an error.
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
