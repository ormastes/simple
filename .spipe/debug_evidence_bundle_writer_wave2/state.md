# Feature: Debug Evidence Bundle Writer (Dump/Replay Wave 2, first slice)

## Raw Request
go parallel — continue the debug/spipe goal with the plan's next admissible step

## Task Type
feature

## Refined Goal
Ship the first producer of `debug-evidence-bundle-v1` bundles — manifest + service receipts + an all-`Unverified` state capsule — proven by a round trip through the existing reader, and clear the two debug remains recorded (not fixed) in Wave 0.

## Acceptance Criteria
- AC-1: `write_debug_evidence_bundle_v1(root, build_id, artifacts)` writes `manifest.sdn`, `receipts.sdn`, `artifacts/<name>`, `normalized/state_capsule.sdn`; `inspect_debug_evidence_bundle_v1(root)` returns `Ok` on the result with matching session/build ids and artifact count.
- AC-2: The writer fails closed on: malformed `build_id`; missing artifact; duplicate artifact basename; a root that already holds `manifest.sdn`; empty artifact list.
- AC-3: The emitted state capsule validates and every one of its six capabilities is `Unverified` — a bundle never implies capability.
- AC-4: `simple debug write <root> --build-id sha256:<hex> <artifact>...` is dispatched in `cli_debug/main.spl`; `debug_evidence_bundle_contract.md` and `state_capability_receipt_contract.md` no longer say the producer does not exist.
- AC-5: `probe_executor_v1.spl` and `interpreter_service_adapter_v1.spl` compile: `_authorize_at`, `_record_at`, `_apply_probe`, `DebugProbeKindV1`, `Probe` defined once each with the signatures the callers already use; two specs; existing debug specs stay GREEN.
- AC-6: The two RED specs importing `debug_wire_v1` / `sdb_command_contract_v1` are either GREEN via a corrected import or recorded with the deleting/never-existing commit evidence.
- AC-7: Every spec touched scores 90 on `sspec-train.shs`.

## Scope Exclusions
- ELF core / minidump / Mach-O / firmware / T32 importers (rest of Wave 2): each needs a real artifact fixture; none exists in-tree.
- Any capability above `Unverified`; any checkpoint/replay (Waves 3–4).
- `legacy_service_adapter_v1.spl` (missing module used by a legacy spec) — recorded, not created.

## Cooperative Review
W6 (Opus) writer + CLI + docs; W7 (Opus) service symbols; W8 (Sonnet) missing-module specs. Disjoint files — W6 reads but does not edit `service_v1.spl`/`contracts_v1.spl`, which W7 owns. Orchestrator (Fable) re-runs every reported spec and the two Wave 0 specs as regression before commit.

## Runtime Boundary Decision
- runtime_need: file write/copy, sha256, clock — all via existing facades.
- facade_checked: `std.nogc_sync_mut.io.file_ops`, `std.crypto.sha256`, the clock facade the reader already uses.
- chosen_path: reuse-facade.
- rejected_shortcuts: overwriting an existing bundle; deriving `build_id` from anything but an explicit `sha256:` argument; emitting any capability other than `Unverified`.

## Research Summary
### Existing Code
- `src/app/cli_debug/evidence_inspect_v1.spl` — reader; parses `schema`, `session_id`, `build_id`, `captured_at_ns`, `artifacts` (`- path:` / `digest:`), `receipts_digest`; sha256-verifies artifacts.
- `src/lib/common/debug/service_v1.spl` — `_open`, `_authorize`, `_record` (assigns `receipt_id`), `_record_outcome`, `_session_count`.
- `src/lib/common/debug/state/capability_receipt_v1.spl` — `..._unverified_v1`, `..._validate_v1`.
- `doc/08_tracking/bug/debug_service_v1_probe_and_adapter_call_undefined_symbols_2026-09-05.md` — the W7 target list.
- `test/fixtures/debug/evidence_bundle_contract_v1*` — hand-built valid bundle.
### Risks
- The reader's SDN parsing is line-shaped; the writer must emit exactly that shape (round-trip spec is the guard).
- `Probe` added to `DebugRootOperationV1` may break an exhaustive `match` — W7 greps first.

<!-- sdn-diagram:id=debug_evidence_bundle_writer_wave2.research -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_evidence_bundle_writer_wave2.research hash=sha256:auto render=ascii
@layout dag
@direction LR

Artifacts -> Writer
Writer -> ServiceV1
ServiceV1 -> ReceiptsSdn
Writer -> ManifestSdn
Writer -> StateCapsuleSdn
ManifestSdn -> Reader
ReceiptsSdn -> Reader
StateCapsuleSdn -> Validator
```

</details>
<!-- sdn-diagram:end -->

## Phase Checklist
- [x] 1-dev
- [x] 2-research
- [x] 3-arch (design: `doc/05_design/app/debug/debug_capability_truth_wave0_design.md` § Writer admissibility; plan Wave 2 row)
- [ ] 4-spec (W6/W7/W8 write specs first)
- [ ] 5-implement (lanes running)
- [ ] 6-refactor
- [ ] 7-verify
- [ ] 8-ship
