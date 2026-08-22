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

## Environment plan and replay

The extractor writes strictly increasing instructions into a caller buffer and seals a digest. The executor validates capability, safety policy, capacity, and sequence before applying any instruction. Plan-Then-Commit performs the accepted plan once; ReplayOnly feeds recorded observations to shadow providers. A provider requesting an unrecorded or different interaction returns `InvalidRequest`/`Diverged`, never ambiently performs it.

## Fixed-capacity behavior

Every manifest declares required frame depth, event words, trace operations/bytes, request/result bytes, diff rows, deadlines, and log bytes. Initialization either supplies them completely or fails. At exact capacity, the final valid record succeeds. Capacity+1 sets sticky overflow with kind, first sequence, and count; no diagnostic allocation occurs. The combined default event/log capacity is <=4 MiB and may be configured downward.

## Migration verifier

The verifier uses compiler-resolved declarations and entry closures. Its baseline fingerprint is `(rule_id, canonical_module, symbol, source_span, normalized_signature)`. Candidate recording never modifies the accepted baseline. Receipt status passes only when new/changed/stale/malformed/expired counts are zero and every pre-milestone warning exactly matches the baseline; at/after milestone total findings and baseline entries must both be zero.

## Error handling

All APIs return `Result<T, E>` or closed status values. Unknown dispatch arms, schema versions, providers, opcodes, comparators, normalizers, predicates, and receipt fields are catchable failures. No abort/unreachable fallback is permitted. Overflow, timeout, child crash, malformed receipt, pack failure, stale exclusion, and allocation violation preserve actionable bounded provenance.

## Performance implementation notes

- Per-thread fixed shards; one compact commit per decision evaluation.
- Static tables sorted once; no hot-path registry construction.
- Dense runtime slots with stable semantic IDs retained in manifests/receipts.
- No locks, dictionaries, formatting, I/O, env reads, timestamps, or loader calls in probe paths.
- Persistent isolated workers amortize startup; isolation setup costs remain separately reported.
- Offline rendering turns binary receipts into intensive human logs.

## Compatibility

Existing `std.mcdc` analysis APIs become a facade over the canonical model. Global registration/growing evaluation APIs and Boolean `coverage` config warn only for exact untouched legacy fingerprints. Existing I/O APIs delegate to tagged operations during the migration; raw aliases and app-owned HAL paths are forbidden.

