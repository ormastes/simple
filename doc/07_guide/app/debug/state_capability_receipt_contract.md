# State Capability Receipt Contract (v1) — pure-data contract

## Status (read this first)

**A pure-data contract exists. A producer does not.** This is Wave 0 of the
dump/replay design plan: freeze `StateCapabilityReceiptV1` as a value type
with a constructor and a validator, before any capsule producer is built.

- **Contract module (exists, real):**
  `src/lib/common/debug/state/capability_receipt_v1.spl` —
  `state_capability_receipt_unverified_v1` (default constructor),
  `state_capability_receipt_validate_v1` (pure validator). No I/O.
- **Spec pinning this contract:**
  `test/01_unit/lib/common/debug/state_capability_receipt_v1_spec.spl`.
- **Producer (does not exist yet):** nothing in this repo emits a real
  `StateCapabilityReceiptV1` from a captured artifact. That is later waves of
  `doc/01_research/infra/dump_replay/simple_dump_replay_fw_spipe_devhub_design_plan_2026-09-05.md`.

## Source of truth

Field list, `CapabilityStatus`, and resource dispositions are frozen
verbatim from that design doc's section 5 (~L226-320). Reconcile this file
with the doc if either drifts.

## Fields

| Field | Type | Rule |
|---|---|---|
| `receipt_version` | text | must equal `state-capability-receipt/v1` |
| `artifact_id` | text | non-empty |
| `raw_artifact_digests` | `[text]` | each entry, if present, must be `sha256:<64 lowercase hex>` |
| `normalized_capsule_digest` | text | empty or `sha256:<64 lowercase hex>` |
| `target_id`, `target_revision`, `build_identity`, `engine_id`, `engine_version`, `machine_config_digest` | text | not validated in v1 (identity fields, opaque to this contract) |
| `state_granularity`, `capture_boundary`, `capture_perturbation` | text | not validated in v1 |
| `components_present`, `components_missing` | `[text]` | not validated in v1 |
| `resource_dispositions` | `[text]` | not validated in v1 (see `ResourceDisposition` below for the vocabulary) |
| `analyze`, `resume_forward`, `exact_replay`, `reverse_execution`, `counterfactual_fork`, `profile_correlation` | `CapabilityStatus` | `Supported` requires a non-empty `proof_receipts` |
| `proof_receipts` | `[text]` | must be non-empty if any capability is `Supported` |
| `taints`, `safety_class`, `redaction_receipt` | text/list | not validated in v1 |

## `CapabilityStatus` — not Boolean

```
Supported
Partial(reason, boundary)
Blocked(reason, missing_evidence)
Unavailable(reason)
Prohibited(policy)
Unverified(claim_source)
```

Evidence each status implies:
- `Supported` — a runnable acceptance receipt exists (`proof_receipts`
  non-empty); enforced by the validator.
- `Partial` — works only within a stated `boundary`; the `reason` explains
  the limitation.
- `Blocked` — could work in principle but `missing_evidence` names what is
  absent.
- `Unavailable` — not offered for this artifact/engine; `reason` says why.
- `Prohibited` — disallowed by `policy` (safety/licensing), regardless of
  technical feasibility.
- `Unverified` — claimed but not checked; `claim_source` names who/what
  asserted it. **This is the default** — see the rule below.

## `ResourceDisposition` vocabulary

`Restored | Replayed | Recreated | Proxied | Frozen | ResetAtBoundary |
ModeledByScenario | OmittedAnalysisOnly | Unsupported | Prohibited` — ten
dispositions a component can carry; not yet validated against
`resource_dispositions` entries in v1.

## The Wave 0 rule

**Unverified by default.** `state_capability_receipt_unverified_v1` sets all
six capability fields to `Unverified(claim_source)` and every list empty —
a capsule must never imply capability merely because it contains bytes.

**No Supported without proof.** `state_capability_receipt_validate_v1`
rejects any receipt where a capability is `Supported` but `proof_receipts`
is empty. This is the only cross-field rule enforced in v1.

## Producer (does not exist yet)

Mirroring `debug_evidence_bundle_contract.md`: nothing in this repo
constructs a `StateCapabilityReceiptV1` from a real capture. A future
producer must call `state_capability_receipt_unverified_v1` first, then only
promote a capability to `Supported` after recording a proof receipt —
never construct one directly with a hand-picked status.

## Related

- Design doc: `doc/01_research/infra/dump_replay/simple_dump_replay_fw_spipe_devhub_design_plan_2026-09-05.md`
  section 5 (contract), section 22 (repository placement).
- Sibling contract: `doc/07_guide/app/debug/debug_evidence_bundle_contract.md`.
