# Feature: Debug Capability Truth (Dump/Replay Wave 0)

## Raw Request
/goal improve debug, spipe infra with last research doc, research more and complete training feature. impl with spipe skill. make design and plan doc or update. go in parallel

## Task Type
feature

## Refined Goal
Execute Wave 0 of `doc/01_research/infra/dump_replay/simple_dump_replay_fw_spipe_devhub_design_plan_2026-09-05.md` — lock the capability contract, complete the existing evidence READER, and reset overstated replay labels — without building any new engine.

## Acceptance Criteria
- AC-1: `StateCapabilityReceiptV1` + `CapabilityStatus` (six arms, verbatim payloads) + `ResourceDisposition` exist as pure data in `src/lib/common/debug/state/capability_receipt_v1.spl`; the only constructor yields all six capabilities `Unverified`; the validator rejects `Supported` with empty `proof_receipts`, a malformed digest, and a wrong `receipt_version`. Conformance spec runs on the seed.
- AC-2: `simple debug inspect` completes on a hand-built valid bundle: `evidence_inspect_v1_spec.spl` and the contract spec's happy path are GREEN on the seed; the `receipt_id` defect is resolved with a reproduction + generalization spec; policy-ctor imports point at `service_v1`.
- AC-3: Every `central_debug_service_v1_*` symbol that a caller invokes but nothing defines is either defined once in `service_v1.spl` (read-path callers) or listed with file:line in a bug record (probe/adapter callers).
- AC-4: Each of the seven §4.2 relabels is checked against source and recorded CONFIRMED/REFUTED/PARTIAL with the decisive function; `doc/07_guide/app/tools/sreplay.md` and user-visible help strings carry the agreed label, never a stronger one.
- AC-5: `doc/07_guide/app/debug/state_capability_receipt_contract.md` and `debug_profile/skill.md` are refreshed in the same commits as the code.

## Scope Exclusions
- The bundle WRITER (addendum Wave 2) and any dump capture/parser. The reader must complete first; the plan doc records when the writer becomes admissible.
- `probe_executor_v1.spl` / `interpreter_service_adapter_v1.spl` repair — recorded, not fixed.

## Cooperative Review
W2 (Sonnet) contract; W3 (Opus) reader reconciliation; W4 (Sonnet) truth reset. Disjoint files. Orchestrator (Fable) re-runs every spec each lane reports before commit; a lane's PASS claim is not accepted without the recorded binary identity.

## Runtime Boundary Decision
- runtime_need: none new; sha256 via existing stdlib.
- facade_checked: `DebugReceiptV1`/`service_v1` are the facade; extend in place.
- chosen_path: reuse-facade.
- rejected_shortcuts: adding a `receipt_id` field that nothing assigns; a `Supported` status without a proof receipt.

## Research Summary
### Existing Code
- `src/lib/common/debug/contracts_v1.spl:59-67` — `DebugReceiptV1` (no `receipt_id`).
- `src/lib/common/debug/service_v1.spl` — 5 public fns; `_record_outcome`, `_apply_probe`, `_authorize_at`, `_record_at`, `_session_count` are called (6 sites) but undefined.
- `src/app/cli_debug/evidence_inspect_v1.spl:96,137,159` — reads `manifest.sdn`/`receipts.sdn`, digest-verifies, then dies on `receipt_id`.
- `src/app/cli_debug/evidence_replay_v1.spl:111-136` — `.sst` selection; same `receipt_id`; hard-codes `deterministic: true`.
- `doc/07_guide/app/debug/debug_evidence_bundle_contract.md` — pinned contract, "Writer (does not exist)".
- Addendum §4.2, §5, §17 Wave 0, §22 — labels, receipt schema, gate, paths.
### Risks
- The addendum audited via GitHub code search and never names `evidence_inspect_v1.spl`/`evidence_replay_v1.spl`; its relabels may be wrong in either direction — W4 verifies each against source before writing it into a guide.

<!-- sdn-diagram:id=debug_capability_truth_wave0.research -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_capability_truth_wave0.research hash=sha256:auto render=ascii
@layout dag
@direction LR

ManifestSdn -> EvidenceInspect
ReceiptsSdn -> EvidenceInspect
EvidenceInspect -> DebugServiceV1
DebugServiceV1 -> DebugReceiptV1
CapabilityReceiptV1 -> Validator
Writer -x EvidenceInspect
```

</details>
<!-- sdn-diagram:end -->

## Verification (2026-09-05, orchestrator re-ran every lane's spec; seed `src/compiler_rust/target/bootstrap/simple`, 22744272 B, Sep 5 12:35, bootstrap-seed banner; `$B test` = unknown command, `$B run` used)

| AC | evidence | verdict |
|---|---|---|
| AC-1 | `$B run test/01_unit/lib/common/debug/state_capability_receipt_v1_spec.spl` → `outcome=OK executed=5 passed=5 failed=0`; guide has "Producer (does not exist yet)" | PASS — commit `9e19fa61338` |
| AC-2 | `evidence_inspect_v1_spec.spl` → `executed=5 passed=5`; `debug_evidence_bundle_contract_v1_spec.spl` → `executed=7 passed=7` (happy path was RED); receipt_id resolved with reproduction + generalization `it`; ctors imported from `service_v1` | PASS — commit `9521b2d4f14` |
| AC-3 | `_record_outcome`, `_session_count` defined once in `service_v1.spl`; `_apply_probe`, `_authorize_at`, `_record_at`, `_receipts`, `DebugProbeKindV1`, `.Probe` recorded with file:line in `doc/08_tracking/bug/debug_service_v1_probe_and_adapter_call_undefined_symbols_2026-09-05.md` | PASS |
| AC-4 | seven rows CONFIRMED against source (two understated by the plan: container restore = unconditional `Ok(nil)`; zero `ReplayableDevice` impls — the only "impl" hit is the comment claiming they all do); guide relabelled 0→10 label mentions; help strings checked, no change needed | PASS — commit `cf800a9376c` |
| AC-5 | `state_capability_receipt_contract.md` new; `debug_profile/skill.md` +18 lines, same commits as code | PASS |

Pre-existing RED, untouched, not this lane's: `service_commands_v1_spec.spl` (2/5, `debug_wire_v1` undefined) and `debug_service_harmony_spec.spl` (0/2, `sdb_command_contract_v1` undefined) — grep 0 definitions in `src/`. `offline_provenance_v1.spl` (third `_record_outcome` caller) has no spec: UNVERIFIED.

Not done in this lane, by design: the bundle WRITER. Admissible now that AC-1 + AC-2 hold (see design § Writer admissibility).

## Phase Checklist
- [x] 1-dev
- [x] 2-research
- [x] 3-arch (design: `doc/05_design/app/debug/debug_capability_truth_wave0_design.md`)
- [x] 4-spec (W2/W3 specs written before code; contract happy path was the RED)
- [x] 5-implement (W2 `9e19fa61338`, W3 `9521b2d4f14`, W4 `cf800a9376c`)
- [x] 6-refactor (diffs reviewed: one counter, one delegate, no unused symbol; sha256 helper reused)
- [x] 7-verify (table above)
- [x] 8-ship

### 8-ship
Landed on PR #371 branch `work/debug-perf-dump-skills-2026-09-05` (shas as of the first rebase — later rebases rewrite them; resolve by subject): `9e19fa61338` (receipt contract), `9521b2d4f14` (reader completes), `cf800a9376c` (SReplay relabels), plus the closing commit that types `resource_dispositions` as `[ResourceDisposition]` (the enum was otherwise unreferenced; spec re-run 5/5). Doc/wiki refresh in the same commits: `state_capability_receipt_contract.md`, `sreplay.md`, `debug_profile/skill.md` (+ Lane docs pointer), design, wave plan. Two bug records filed (`debug_service_v1_probe_and_adapter_call_undefined_symbols`, `sreplay_capability_labels_overstate_implementation`); one resolved (`debug_evidence_inspect_receipt_id_field_missing`). Numbered-artifact guard (`sh scripts/audit/numbered-artifact-guard.shs --changed-from origin/main`): `PASS — 12 path(s) classified in --changed-from, 0 numbered artifacts`. Pre-existing RED left RED and named in Verification. Next admissible wave: the bundle WRITER (plan § Wave 2), entry conditions now met.
