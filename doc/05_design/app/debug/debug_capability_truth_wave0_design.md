# Debug Capability Truth (Dump/Replay Wave 0) — Design

**Date:** 2026-09-05 · **State:** `.spipe/debug_capability_truth_wave0/state.md` · **Plan:** `doc/03_plan/app/debug/dump_replay_wave_plan.md`
**Research:** `doc/01_research/infra/dump_replay/simple_dump_replay_fw_spipe_devhub_design_plan_2026-09-05.md` §4–§5, §17 Wave 0, §22; provenance caveats in `doc/01_research/infra/dump_replay/PROVENANCE.md`

## Decision

Wave 0 of the addendum is "capability truth and contract lock": no new engine, no `Supported` without a
runnable acceptance receipt, `Unverified` by default, and a relabel of six replay components the design
found over-described. This design executes exactly that and adds one item the addendum could not see.

The addendum treats `DebugServiceV1` and `DebugEvidenceBundleV1` as existing architecture to extend. In
this tree the *reader* exists (`evidence_inspect_v1.spl` digest-verifies a `manifest.sdn`) but cannot
complete: it reads a `receipt_id` the receipt record lacks, imports policy constructors from the wrong
module, and — with five other callers — invokes `central_debug_service_v1_*` functions nothing defines.
`DebugEvidenceBundleV1` as a type does not exist; only the contract doc does. So the first truth to reset
is the service surface itself, and the reader is completed *before* any writer is admissible.

Three lanes, disjoint files: **contract** (`StateCapabilityReceiptV1` as pure data with a validator that
enforces the Wave 0 gate), **reader** (define the read-path symbols once, resolve `receipt_id`, two specs
per fix, record probe/adapter callers as non-compiling), **truth reset** (verify each §4.2 relabel against
source — the addendum audited via code search — then relabel guide + help strings).

<!-- sdn-diagram:id=debug_capability_truth_wave0.design -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_capability_truth_wave0.design hash=sha256:auto render=ascii
@layout dag
@direction LR

Operator -> DebugInspectCli
DebugInspectCli -> EvidenceInspectV1
EvidenceInspectV1 -> ManifestSdn
EvidenceInspectV1 -> ServiceV1
ServiceV1 -> DebugReceiptV1
CapabilityReceiptV1 -> ReceiptValidator
ReceiptValidator -> ProofReceipts
BundleWriter -x ManifestSdn
```

</details>
<!-- sdn-diagram:end -->

## Interfaces

| module | contract |
|---|---|
| `src/lib/common/debug/state/capability_receipt_v1.spl` | `enum CapabilityStatus { Supported, Partial(reason, boundary), Blocked(reason, missing_evidence), Unavailable(reason), Prohibited(policy), Unverified(claim_source) }`; `enum ResourceDisposition` (10 arms); `struct StateCapabilityReceiptV1` (addendum §5 fields verbatim); `state_capability_receipt_unverified_v1(artifact_id, claim_source)`; `state_capability_receipt_validate_v1(r) -> Result<(), text>` |
| validator rejects | `receipt_version != "state-capability-receipt/v1"`; empty `artifact_id`; digest not `sha256:`+64 lc hex; any of six statuses `Supported` with `proof_receipts` empty |
| `service_v1.spl` additions | `central_debug_service_v1_record_outcome` (one definition, delegates to `_record`), `_session_count`; policy ctors stay here and callers import from here |
| `DebugReceiptV1` | `receipt_id` added ONLY if inspection output needs a stable id and `_authorize`/`_record` assign it; otherwise callers use `succeeded`/`allowed` — W3 decides and justifies |
| relabels | seven rows, each CONFIRMED/REFUTED/PARTIAL with file:line before the guide changes |

## Writer admissibility (explicitly deferred)
A `manifest.sdn` writer (addendum Wave 2) may start only when: reader specs GREEN on the seed; contract
validator GREEN; `StateCapabilityReceiptV1` frozen. The writer's first output must validate under both.
