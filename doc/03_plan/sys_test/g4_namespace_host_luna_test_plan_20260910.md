# G4 namespace/head/recovery test handoff (Luna)

Status: scoped test implementation; physical host-provider admission is
`MissingEvidence` until a qualified provider proves a descriptor-bound host
capability.

## Frozen interfaces

| Interface | Owner contract | Test oracle |
|---|---|---|
| `cache_cooperative_namespace_host_next_missing_v1(inventory)` | Diagnostic prerequisite order; never authority | Each of the 11 flags false in isolation, then all true => `Ready` |
| `cache_cooperative_namespace_host_admission_preflight_v1(...)` | Pure typed validation/refusal; never authority | Invalid head, invalid writer, and current `ImmutableSyncUnavailable` refusal |
| `cache_cooperative_namespace_host_admit_existing_head_v1(...)` | Closed issuer; host-issued combined capability is required | Physical admission remains `MissingEvidence`; no test constructs or invokes opaque handles |
| `cache_cooperative_selected_head_encode/decode_v1` | Canonical checksummed selected-head wire form | Round trip, wrong magic, noncanonical integer, oversize, bounds 0/-1/max/max+1 |
| `cache_cooperative_namespace_revalidation_v1` | Whole-head and writer-incarnation comparison | `Current`, `StaleHead`, `StaleWriter` |
| `cache_cooperative_durability_trace_valid/outcome_v1` | Ordered durable prefix and post-replacement uncertainty | Legal prefixes reject-before-replace; any replacement evidence is `Indeterminate` unless fully synced |

## Executable scenarios

`test/02_integration/compiler/cache/cooperative_namespace_host_admission_spec.spl`
contains real assertions for the diagnostic, selected-head, preflight,
revalidation, and durability rows above. Physical admission itself is an unexecuted
`MissingEvidence` row because no host issuer exists. Existing unit coverage
remains in `test/01_unit/compiler/cache/cooperative_namespace_host_prerequisite_v1_spec.spl`.

Physical provider rows intentionally do not construct fake handles. The spec
records the missing authority and checks the production prerequisite remains
closed; the next host-authority handoff must replace that row with a real
descriptor-bound provider receipt and measured recovery evidence.

## Sol review guide

Sol should check only the frozen API names/field meanings and the exact manifest:

1. Every missing-prerequisite enum is reached with one false flag while later
   flags remain true; all-present is tested separately.
2. Selected-head tests include negative, zero, maximum, maximum-plus-one,
   invalid generation/digest/checksum, malformed prefixes, bad magic,
   noncanonical integer spelling, newline/NUL, and oversize input.
3. Admission has no executable fake-handle case; its physical row remains
   `MissingEvidence` until the issuer exists.
4. Revalidation compares all selected-head identity fields and writer epoch,
   including invalid heads and negative writers.
5. Recovery tests cover valid prefixes, ordering violations, and all replace
   markers; only confirmed replacement plus directory sync is committed.
6. No physical E2E claim is made without a host receipt, serial/transcript, or
   durable recovery artifact.

Coverage evidence is not yet measured at the required 95% threshold. The
executable slice exercises API-completeness short circuits, every selected-head
identity field, and confirmed-but-unsynced replacement. Physical host
admission, issuer validation, and provider rows remain `MissingEvidence`.

| Component | Current evidence | Remaining gate |
|---|---|---|
| namespace host prerequisite | unit/component assertions; unmeasured | admitted self-hosted branch receipt |
| namespace limit/preflight | unit assertions; unmeasured | admitted self-hosted branch receipt |
| selected-head reopen | unit assertions; unmeasured | admitted self-hosted branch receipt |
| GC contribution preflight | unit assertions; unmeasured | admitted self-hosted branch receipt |
| selected-head publisher | RED dependency row; diagnostic preflight only | reviewed G3 durable publisher lands first; prior-head CAS remains physical `MissingEvidence` |
| physical namespace/provider | `MissingEvidence` | continuous root gate, sync/replace/dir-sync and independent reopen proof |

Performance debt: `action_root_journal_find_operation_v1` hashes prior prefixes
while scanning, which is worst-case quadratic in selected record count. Reopen
qualification requires a measured startup bound or a semantics-preserving
single-pass/indexed replacement before production admission.

## Astra final review guide

Astra reviews the isolated diff and accepts only if the source/test manifest is
conserved, assertions are behavior-level (not source-string or `true == true`),
and `MissingEvidence` remains explicit. The production gate stays closed until
the host authority supplies immutable sync, head replacement, directory sync,
restart reissue, complete namespace union, and qualified physical evidence.
