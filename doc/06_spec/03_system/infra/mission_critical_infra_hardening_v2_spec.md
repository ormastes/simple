# Mission-Critical Infrastructure Hardening V2 — Operator Manual

**Evidence class:** executable pure-policy validation plus explicit release blockers
**Executable source:** `test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl`
**Executable source SHA-256:** `58c24ea2d717bee9e4c2b09622702e41df7c2d5c02b90648526e87f221ce6d7b`
**Generation status:** hand-maintained mirror; SPipe doc generation is blocked by the known compiler conflict in `src/compiler/70.backend/backend/runtime_compiler.spl` and was not run.

## Claim boundary

This flow proves deterministic behavior of the implemented pure-Simple policies and the controlled producer contracts named below. An `evidence-contract` row records only that narrower contract coverage; it does **not** claim that live external tooling ran, that a real guest or graphics device was exercised, that a real RenderDoc capture was validated, or that any platform completed the required 24-hour stress campaign. Those missing live evidence classes keep every affected release scenario blocked.

## Operator flow

1. **Prepare an isolated mission-critical evidence run**
   Create an in-memory correlated run identity. No cached or external evidence is imported.

2. **Admit exact-current compiler and tooling artifacts**
   Validate a versioned collector receipt bound to run, source, configuration,
   toolchain, dependency, environment, input bundle, resolved executable,
   parent pure-Simple lineage, and the complete ordered discriminating-fixture
   manifest. Repeat with stale lineage and require `stale_lineage`. This
   exercises the pure admission half of REQ-MCI-001; collection and the unified
   external tooling matrix in REQ-MCI-002 remain blocked.

3. **Exercise the certified SimpleOS platform manifest**
   Validate the exact canonical 4-host × 6-guest catalog with two selected,
   canonical serialization and a SHA-256 content hash. Unselected cells carry
   no present/passing receipt state; selected cells bind four guest payload
   artifact hashes and a correlated 24-hour stress receipt.
   correlated, fresh, hash-bound cells and 22 explicitly unselected cells.
   Require `certified-subset-pass`, exactly 24 visible rows, and
   `umbrella_all_platforms = false`. This is not guest/QEMU execution evidence.

4. **Exercise packed rendering and backend provenance**
   Count-plan and admit exactly eight rows/64 bytes, preserve arena and generation identity, seal, and retire. Then request nine rows and require `DRAW_IR_OVERFLOW_COUNT` before admission. This covers the packed-generation bounds in REQ-MCI-005 and NFR-MCI-006. Real device provenance, structured UI interaction, exact readback, and RenderDoc evidence required by REQ-MCI-006 remain blocked.

5. **Exercise strict and relaxed allocation profiles**
   Allocate the exact 64-byte sealed domain quota, reject the next byte with
   `ARENA_EXHAUSTION_QUOTA`, roll back the private staging generation, reject
   ISR allocation with `ARENA_EXHAUSTION_FORBIDDEN_CONTEXT`, and roll back
   again. Unit evidence additionally proves forged checkpoints fail and a later
   staging rollback preserves the prior committed generation. This is policy
   validation, not a whole-runtime zero-allocation trace or complete injection campaign.

6. **Exercise bounded process policy without launching a host process**
   Reject PID `-1` and `0`, reject work beyond a fixed queue, admit exact
   capture and timeout capacity, reject one unit beyond each limit, and keep
   worker width distinct from subprocess in-flight capacity. Drive the pure
   `admitted -> running -> cancel_requested -> timed_out` lifecycle, also prove
   `running -> completed`, reject terminal re-entry, and require invalid PIDs
   to expose neither signal nor wait intent. This is policy-level coverage only.

7. **Verify freshness, bounds, isolation, and performance budgets**
   Check retired DrawIR generation identity, absence of a committed allocation
   generation after rollback, monotonic next-generation identity, and
   allocation high-water. No latency/RSS/stress measurements are manufactured.

8. **Review the fail-closed aggregate evidence manifest**
   Feed one valid local receipt into the real `HardeningEvidenceMatrix` policy
   while requiring an absent external-host receipt. Require a non-empty blocker
   ledger and aggregate **BLOCKED**, never PASS.

## Traceability and evidence status

| Requirement | Executable evidence in this scenario | Current classification |
|---|---|---|
| REQ-MCI-001 | Exact-current admission plus stale negative control | Exercised |
| REQ-MCI-003, REQ-MCI-004 | Certified subset, 24 visible cells, canonical payload fields, no umbrella claim | Policy exercised; real guest execution blocked |
| REQ-MCI-005 | Exact-capacity DrawIR plan/admit/seal/retire and +1 rejection with identity | Exercised |
| REQ-MCI-007, REQ-MCI-008 | Sealed quota, forbidden ISR context, quota exhaustion, rollback, telemetry | Exercised |
| REQ-MCI-009 policy subset | PID, queue, distinct in-flight, capture, timeout, cancellation, terminal, and invalid-transition boundaries | Policy exercised only; owner-facade signal/wait/process integration remains **BLOCKED** |
| REQ-MCI-010 | Focused policy aggregate blocks on a missing external receipt. Collector mechanics `MCI-AGG-001/002/003` are owned by and linked to `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs`. | Collector contract PASS; release aggregate **BLOCKED** |
| REQ-MCI-011 | Executable source and this operator mirror | Present; generated-doc freshness receipt blocked |
| NFR-MCI-003 policy subset; NFR-MCI-004, NFR-MCI-006 | Bounded timeout/capture/queue/in-flight policy, arena quota, DrawIR count bounds | Deterministic policy subset exercised; real hung/flooding child evidence remains **BLOCKED** |
| REQ-MCI-002, REQ-MCI-006; NFR-MCI-001/002/005/007/008/009 | External/tool/device/campaign/reviewer evidence | **BLOCKED — not faked** |

## Frozen scenario classification matrix

These rows are traceability classifications, not claims that the system SSpec
executed the named scenario. `evidence-contract` links narrower executable
contract evidence; `blocked` names the missing release-grade owner or evidence.

| Scenario | Class | Owner/evidence | Status/reason | Resume prerequisite |
|---|---|---|---|---|
| MCI-AGG-001 | evidence-contract | `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` | `collector-contract-only` | `run-release-gate-after-all-receipts` |
| MCI-AGG-002 | evidence-contract | `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` | `collector-contract-only` | `run-release-gate-after-all-receipts` |
| MCI-AGG-003 | evidence-contract | `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` | `collector-contract-only` | `run-release-gate-after-all-receipts` |
| MCI-ALLOC-001 | evidence-contract | `test/01_unit/scripts/mci_v2_allocation_contract_test.shs` | `allocation-contract-only` | `sign-current-allocation-producer-receipt` |
| MCI-ALLOC-002 | evidence-contract | `test/01_unit/scripts/mci_v2_allocation_contract_test.shs` | `allocation-contract-only` | `sign-current-allocation-producer-receipt` |
| MCI-ALLOC-003 | evidence-contract | `test/01_unit/scripts/mci_v2_allocation_contract_test.shs` | `allocation-contract-only` | `sign-current-allocation-producer-receipt` |
| MCI-ALLOC-004 | evidence-contract | `test/01_unit/scripts/mci_v2_allocation_contract_test.shs` | `allocation-contract-only` | `sign-current-allocation-producer-receipt` |
| MCI-ALLOC-005 | evidence-contract | `test/01_unit/scripts/mci_v2_allocation_contract_test.shs` | `allocation-contract-only` | `sign-current-allocation-producer-receipt` |
| MCI-ALLOC-006 | evidence-contract | `test/01_unit/scripts/mci_v2_allocation_contract_test.shs` | `allocation-contract-only` | `sign-current-allocation-producer-receipt` |
| MCI-COMP-001 | evidence-contract | `test/01_unit/scripts/mci_v2_compiler_admission_contract_test.shs` | `fixed-compiler-fixture-contract-only` | `run-authenticated-current-compiler-producer` |
| MCI-COMP-002 | blocked | `scripts/check/check-mci-v2-compiler-admission.shs` | `cross-host-signed-peer-missing` | `run-independent-host-and-sign-peer-receipt` |
| MCI-COMP-003 | blocked | `scripts/check/check-mci-v2-compiler-admission.shs` | `live-negative-campaign-not-admitted` | `run-current-live-negative-campaign` |
| MCI-DOC-001 | blocked | `bin/simple-spipe-docgen` | `docgen-receipt-absent` | `resolve-runtime-compiler-conflict-and-run-docgen-once` |
| MCI-DOC-002 | blocked | `bin/simple-spipe-docgen` | `generated-helper-visibility-unverified` | `resolve-runtime-compiler-conflict-and-run-docgen-once` |
| MCI-DOC-003 | evidence-contract | `test/01_unit/scripts/mci_v2_traceability_contract_test.shs` | `negative-traceability-contract-only` | `run-docgen-after-compiler-conflict-resolves` |
| MCI-NFR-001 | evidence-contract | `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` | `freshness-contract-only` | `collect-current-signed-lane-receipts` |
| MCI-NFR-002 | evidence-contract | `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` | `identity-contract-only` | `collect-current-signed-lane-receipts` |
| MCI-NFR-003 | blocked | `scripts/check/check-mci-v2-compiler-admission.shs` | `cross-host-signed-peer-missing` | `run-independent-host-and-sign-peer-receipt` |
| MCI-NFR-004 | blocked | `scripts/check/check-mci-v2-compiler-admission.shs` | `live-corruption-campaign-not-admitted` | `run-current-live-corruption-negative` |
| MCI-NFR-005 | evidence-contract | `test/01_unit/scripts/mci_v2_tooling_admission_contract_test.shs` | `tooling-bounds-contract-only` | `run-live-timeout-capture-and-scan-telemetry` |
| MCI-NFR-006 | evidence-contract | `test/01_unit/scripts/mci_v2_tooling_admission_contract_test.shs` | `tooling-negative-contract-only` | `run-live-hang-flood-and-repeat-scan-controls` |
| MCI-NFR-007 | evidence-contract | `test/01_unit/scripts/mci_v2_allocation_contract_test.shs` | `allocation-budget-contract-only` | `sign-current-allocation-producer-receipt` |
| MCI-NFR-008 | evidence-contract | `test/01_unit/scripts/mci_v2_allocation_contract_test.shs` | `allocation-budget-contract-only` | `sign-current-allocation-producer-receipt` |
| MCI-NFR-009 | evidence-contract | `test/01_unit/scripts/mci_v2_allocation_contract_test.shs` | `fault-registry-contract-only` | `sign-current-allocation-producer-receipt` |
| MCI-NFR-010 | evidence-contract | `test/01_unit/scripts/mci_v2_allocation_contract_test.shs` | `rollback-hash-contract-only` | `sign-current-allocation-producer-receipt` |
| MCI-NFR-011 | evidence-contract | `test/01_unit/scripts/mci_v2_rendering_producer_contract_test.shs` | `rendering-budget-fixture-contract-only` | `capture-current-rendering-budget-samples` |
| MCI-NFR-012 | evidence-contract | `test/01_unit/scripts/mci_v2_rendering_producer_contract_test.shs` | `rendering-deadline-contract-only` | `run-live-capacity-and-deadline-negative-controls` |
| MCI-NFR-013 | evidence-contract | `test/01_unit/scripts/mci_v2_tooling_admission_contract_test.shs` | `tooling-metrics-contract-only` | `capture-pinned-warm-tooling-benchmarks` |
| MCI-NFR-014 | evidence-contract | `test/01_unit/scripts/mci_v2_tooling_admission_contract_test.shs` | `tooling-regression-contract-only` | `run-live-configured-regression-negative-controls` |
| MCI-NFR-015 | evidence-contract | `test/01_unit/scripts/mci_v2_stress_contract_test.shs` | `stress-fixture-contract-only` | `complete-current-twenty-four-hour-campaign` |
| MCI-NFR-016 | evidence-contract | `test/01_unit/scripts/mci_v2_stress_contract_test.shs` | `stress-interruption-contract-only` | `run-live-stress-interruption-control` |
| MCI-NFR-017 | evidence-contract | `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` | `focused-reviewer-contract-only` | `obtain-independent-reviewer-receipt` |
| MCI-NFR-018 | evidence-contract | `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` | `focused-reviewer-negative-contract-only` | `obtain-independent-reviewer-receipt` |
| MCI-OS-001 | evidence-contract | `test/01_unit/scripts/mci_v2_simpleos_manifest_contract_test.shs` | `simpleos-manifest-contract-only` | `run-current-guest-matrix` |
| MCI-OS-002 | evidence-contract | `test/01_unit/scripts/mci_v2_simpleos_manifest_contract_test.shs` | `simpleos-matrix-contract-only` | `run-current-guest-matrix` |
| MCI-OS-003 | evidence-contract | `test/01_unit/scripts/mci_v2_simpleos_manifest_contract_test.shs` | `simpleos-negative-contract-only` | `run-current-guest-matrix` |
| MCI-OS-004 | evidence-contract | `test/01_unit/scripts/mci_v2_simpleos_manifest_contract_test.shs` | `simpleos-payload-contract-only` | `run-current-guest-payloads` |
| MCI-OS-005 | evidence-contract | `test/01_unit/scripts/mci_v2_simpleos_manifest_contract_test.shs` | `simpleos-alias-contract-only` | `run-current-guest-payloads` |
| MCI-OS-006 | evidence-contract | `test/01_unit/scripts/mci_v2_simpleos_manifest_contract_test.shs` | `simpleos-payload-negative-contract-only` | `run-current-guest-payloads` |
| MCI-PROC-001 | evidence-contract | `test/01_unit/scripts/mci_v2_process_safety_contract_test.shs` | `process-contract-only` | `admit-current-pure-simple-runner-and-sign-receipt` |
| MCI-PROC-002 | evidence-contract | `test/01_unit/scripts/mci_v2_process_safety_contract_test.shs` | `process-contract-only` | `admit-current-pure-simple-runner-and-sign-receipt` |
| MCI-PROC-003 | evidence-contract | `test/01_unit/scripts/mci_v2_process_safety_contract_test.shs` | `process-contract-only` | `admit-current-pure-simple-runner-and-sign-receipt` |
| MCI-REN-001 | evidence-contract | `test/01_unit/scripts/mci_v2_rendering_producer_contract_test.shs` | `rendering-fixture-contract-only` | `run-live-rendering-producer` |
| MCI-REN-002 | evidence-contract | `test/01_unit/scripts/mci_v2_rendering_producer_contract_test.shs` | `rendering-capacity-contract-only` | `run-live-rendering-producer` |
| MCI-REN-003 | evidence-contract | `test/01_unit/scripts/mci_v2_rendering_producer_contract_test.shs` | `rendering-overflow-contract-only` | `run-live-rendering-producer` |
| MCI-REN-004 | evidence-contract | `test/01_unit/scripts/mci_v2_rendering_producer_contract_test.shs` | `device-ui-fixture-contract-only` | `capture-real-device-ui-and-readback` |
| MCI-REN-005 | evidence-contract | `test/01_unit/scripts/mci_v2_rendering_producer_contract_test.shs` | `renderdoc-fixture-contract-only` | `capture-and-validate-real-renderdoc-artifact` |
| MCI-REN-006 | evidence-contract | `test/01_unit/scripts/mci_v2_rendering_producer_contract_test.shs` | `rendering-negative-contract-only` | `run-live-rendering-negative-controls` |
| MCI-TOOL-001 | evidence-contract | `test/01_unit/scripts/mci_v2_tooling_admission_contract_test.shs` | `tooling-fixture-contract-only` | `run-live-tooling-producer` |
| MCI-TOOL-002 | evidence-contract | `test/01_unit/scripts/mci_v2_tooling_admission_contract_test.shs` | `tooling-bounds-contract-only` | `run-live-tooling-producer` |
| MCI-TOOL-003 | evidence-contract | `test/01_unit/scripts/mci_v2_tooling_admission_contract_test.shs` | `tooling-negative-contract-only` | `run-live-tooling-producer` |

## Required follow-up gates

After the compiler conflict is resolved, run docgen once against `test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl` and retain its zero-stub receipt. The aggregate shell contract may report collector-contract PASS for `MCI-AGG-001/002/003`; that is not release admission. Its ephemeral distinct reviewer keys prove only that valid separately signed decisions pass and missing/self-issued/stale/replayed decisions fail. Release remains BLOCKED pending external tooling, SimpleOS guest, real rendering/RenderDoc, allocation fault-injection, process execution, performance, 24-hour stress, and a receipt from the independently operated reviewer producer. Do not promote the focused fixture to a real review claim.
