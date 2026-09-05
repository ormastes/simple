# mission_critical_infra_hardening_v2_spec

> Mission-critical infrastructure V2 pure-policy acceptance flow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mission_critical_infra_hardening_v2_spec

Mission-critical infrastructure V2 pure-policy acceptance flow.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Mission-critical infrastructure V2 pure-policy acceptance flow.

This executable scenario covers only implemented, deterministic validation
owners.  External-host tooling, real backend/RenderDoc evidence, and the
24-hour platform campaign remain release blockers and are never synthesized as
PASS by this spec.

## Scenarios

### mission-critical infrastructure hardening V2

### REQ-MCI-003 and REQ-MCI-004 policy subset: certified SimpleOS evidence

#### should admit a selected certified guest subset

- should admit a selected certified guest subset
- Exercise the certified SimpleOS platform manifest
   - Expected: result.status equals `pass`
   - Expected: result.selected_cell_count equals `2u32`
   - Expected: result.visible_cell_count equals `24u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-MCI-010 REQ-MCI-003 REQ-MCI-004 REQ-MCI-005 REQ-MCI-007 REQ-MCI-008 REQ-MCI-009 REQ-SSPEC-SYSTEM
step("should admit a selected certified guest subset")
step("Exercise the certified SimpleOS platform manifest")
val result = certified_simpleos_manifest_validate(mci_subset_manifest())
expect(result.status).to_equal("pass")
expect(result.selected_cell_count).to_equal(2u32)
expect(result.visible_cell_count).to_equal(24u32)
```

</details>

#### should retain unselected platform rows without an umbrella claim

- should retain unselected platform rows without an umbrella claim
- Exercise the certified SimpleOS platform manifest
   - Expected: result.visible_cell_count equals `24u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain unselected platform rows without an umbrella claim")
step("Exercise the certified SimpleOS platform manifest")
val result = certified_simpleos_manifest_validate(mci_subset_manifest())
expect(result.umbrella_all_platforms).to_be(false)
expect(result.visible_cell_count).to_equal(24u32)
```

</details>

#### should reject a guest receipt with mismatched host identity

- should reject a guest receipt with mismatched host identity
- Exercise the certified SimpleOS platform manifest
   - Expected: certified_simpleos_manifest_validate(manifest).reason equals `receipt-correlation-mismatch:linux:x86_32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a guest receipt with mismatched host identity")
step("Exercise the certified SimpleOS platform manifest")
var manifest = mci_subset_manifest()
var row = manifest.cells[0]
var boot = row.boot
boot.host_identity = "host-windows"
row.boot = boot
manifest.cells[0] = row
manifest.manifest_hash = certified_simpleos_manifest_hash_v1(manifest)
expect(certified_simpleos_manifest_validate(manifest).reason).to_equal("receipt-correlation-mismatch:linux:x86_32")
```

</details>

### REQ-MCI-005 and NFR-MCI-006 count subset: bounded Draw IR generations

#### should admit an exactly sized packed generation

- should admit an exactly sized packed generation
- Exercise packed rendering and backend provenance
   - Expected: admitted.total_bytes equals `64u64`
   - Expected: admitted.generation equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should admit an exactly sized packed generation")
step("Exercise packed rendering and backend provenance")
val counts = draw_ir_generation_count_v3(2u32, 1u32, 1u32, 1u32, 1u32, 2u32)
val outcome = draw_ir_generation_plan_v3(41u64, 1u64, counts, 8u64, 64u64, 8u64)
var arena = DrawIrGenerationArenaV3.bounded(41u64, 64u64, 8u64)
match outcome:
    DrawIrPlanOutcomeV3.Planned(plan):
        match arena.admit(plan):
            DrawIrAdmissionOutcomeV3.Admitted(admitted):
                expect(admitted.total_bytes).to_equal(64u64)
                expect(admitted.generation).to_equal(1u64)
            DrawIrAdmissionOutcomeV3.Refused(receipt):
                fail("unexpected Draw IR admission refusal")
    DrawIrPlanOutcomeV3.Refused(receipt):
        fail("unexpected Draw IR planning refusal")
```

</details>

#### should seal and retire a published generation

- should seal and retire a published generation
- Exercise packed rendering and backend provenance
   - Expected: admitted.arena_id equals `42u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should seal and retire a published generation")
step("Exercise packed rendering and backend provenance")
val counts = draw_ir_generation_count_v3(2u32, 1u32, 1u32, 1u32, 1u32, 2u32)
val outcome = draw_ir_generation_plan_v3(42u64, 1u64, counts, 8u64, 64u64, 8u64)
var arena = DrawIrGenerationArenaV3.bounded(42u64, 64u64, 8u64)
match outcome:
    DrawIrPlanOutcomeV3.Planned(plan):
        match arena.admit(plan):
            DrawIrAdmissionOutcomeV3.Admitted(admitted):
                expect(admitted.arena_id).to_equal(42u64)
            DrawIrAdmissionOutcomeV3.Refused(receipt):
                fail("unexpected Draw IR admission refusal")
    DrawIrPlanOutcomeV3.Refused(receipt):
        fail("unexpected Draw IR planning refusal")
expect(arena.seal(64u64, 8u64)).to_be_nil()
expect(arena.retire()).to_be(true)
```

</details>

#### should refuse row overflow before admission

- should refuse row overflow before admission
- Exercise packed rendering and backend provenance
   - Expected: receipt.reason equals `DRAW_IR_OVERFLOW_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should refuse row overflow before admission")
step("Exercise packed rendering and backend provenance")
val outcome = draw_ir_generation_plan_v3(
    43u64, 1u64,
    draw_ir_generation_count_v3(9u32, 0u32, 0u32, 0u32, 0u32, 0u32),
    8u64, 64u64, 8u64)
match outcome:
    DrawIrPlanOutcomeV3.Refused(receipt):
        expect(receipt.reason).to_equal(DRAW_IR_OVERFLOW_COUNT)
    DrawIrPlanOutcomeV3.Planned(plan):
        fail("Draw IR overflow was clamped instead of refused")
```

</details>

### REQ-MCI-007 and REQ-MCI-008 policy subset: sealed domain allocation

#### should allocate exactly the sealed domain quota

- should allocate exactly the sealed domain quota
- Exercise strict and relaxed allocation profiles
   - Expected: reference.size_bytes equals `64u64`
   - Expected: arena.high_water_bytes equals `64u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should allocate exactly the sealed domain quota")
step("Exercise strict and relaxed allocation profiles")
var arena = DomainArenaV1.from_sealed_profile(51u64, mci_relaxed_profile())
match arena.try_allocate(64u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Allocated(reference):
        expect(reference.size_bytes).to_equal(64u64)
        expect(arena.high_water_bytes).to_equal(64u64)
    DomainArenaAllocationV1.Exhausted(receipt):
        fail("unexpected exact-quota allocation exhaustion")
```

</details>

#### should return typed exhaustion without advancing publication

- should return typed exhaustion without advancing publication
- Exercise strict and relaxed allocation profiles
   - Expected: reference.size_bytes equals `64u64`
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_QUOTA`
   - Expected: arena.cursor_bytes equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return typed exhaustion without advancing publication")
step("Exercise strict and relaxed allocation profiles")
var arena = DomainArenaV1.from_sealed_profile(52u64, mci_relaxed_profile())
val checkpoint = arena.checkpoint()
val admitted = arena.try_allocate(64u64, ARENA_CONTEXT_NORMAL)
match admitted:
    DomainArenaAllocationV1.Allocated(reference):
        expect(reference.size_bytes).to_equal(64u64)
    DomainArenaAllocationV1.Exhausted(receipt):
        fail("unexpected exact-quota allocation exhaustion")
match arena.try_allocate(1u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_QUOTA)
    DomainArenaAllocationV1.Allocated(reference):
        fail("quota overflow allocation was unexpectedly admitted")
expect(arena.rollback(checkpoint)).to_be(true)
expect(arena.cursor_bytes).to_equal(0u64)
```

</details>

#### should reject allocation in an ISR context

- should reject allocation in an ISR context
- Exercise strict and relaxed allocation profiles
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_FORBIDDEN_CONTEXT`
   - Expected: arena.cursor_bytes equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject allocation in an ISR context")
step("Exercise strict and relaxed allocation profiles")
var arena = DomainArenaV1.from_sealed_profile(53u64, mci_relaxed_profile())
match arena.try_allocate(8u64, ARENA_CONTEXT_ISR):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_FORBIDDEN_CONTEXT)
    DomainArenaAllocationV1.Allocated(reference):
        fail("forbidden-context allocation was unexpectedly admitted")
expect(arena.cursor_bytes).to_equal(0u64)
```

</details>

### REQ-MCI-009 and NFR-MCI-003 policy subset: bounded process policy

#### should admit exact bounded capture and available work

- should admit exact bounded capture and available work
- Exercise bounded concurrency and process failure paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should admit exact bounded capture and available work")
step("Exercise bounded concurrency and process failure paths")
val capture = admit_bounded_capture(BoundedProcessCaptureV1(
    max_stdout_bytes: 16, max_stderr_bytes: 8,
    stdout_bytes: 16, stderr_bytes: 8))
val work = admit_bounded_work(BoundedWorkPoolV1(
    max_workers: 2, max_pending: 1,
    active_workers: 1, pending_work: 1))
expect(capture.accepted).to_be(true)
expect(work.accepted).to_be(true)
```

</details>

#### should reject saturated work and overflowing output

- should reject saturated work and overflowing output
- Exercise bounded concurrency and process failure paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject saturated work and overflowing output")
step("Exercise bounded concurrency and process failure paths")
val work = admit_bounded_work(BoundedWorkPoolV1(
    max_workers: 2, max_pending: 1,
    active_workers: 2, pending_work: 1))
val capture = admit_bounded_capture(BoundedProcessCaptureV1(
    max_stdout_bytes: 16, max_stderr_bytes: 8,
    stdout_bytes: 17, stderr_bytes: 8))
expect(work.accepted).to_be(false)
expect(capture.accepted).to_be(false)
```

</details>

#### should reject nonpositive process identities

- should reject nonpositive process identities
- Exercise bounded concurrency and process failure paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject nonpositive process identities")
step("Exercise bounded concurrency and process failure paths")
expect(validate_process_signal_pid(-1).accepted).to_be(false)
expect(validate_process_signal_pid(0).accepted).to_be(false)
```

</details>

### REQ-MCI-010 evidence-correlation subset: fail-closed aggregation

#### should block an aggregate with a missing required receipt

- should block an aggregate with a missing required receipt
- Review the fail-closed aggregate evidence manifest
   - Expected: result.matrix.result equals `MCI_EVIDENCE_BLOCKED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should block an aggregate with a missing required receipt")
step("Review the fail-closed aggregate evidence manifest")
val hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val policy = MciEvidencePolicyV1(
    schema_version: 1u16, run_id: "mci-system-run",
    source_hash: hash, configuration_hash: hash, now_utc_ns: 1000,
    required_check_ids: ["local-policy", "external-host-tooling"])
var receipt = MciEvidenceReceiptV1(
    schema_version: 1u16, check_id: "local-policy",
    run_id: "mci-system-run", source_hash: hash,
    configuration_hash: hash, valid_until_utc_ns: 1100,
    result: MCI_EVIDENCE_PASS, receipt_hash: "")
receipt.receipt_hash = mci_evidence_receipt_hash(policy, receipt)
val result = aggregate_mci_evidence_v1(policy, [receipt])
expect(result.matrix.result).to_equal(MCI_EVIDENCE_BLOCKED)
expect(result.matrix.blockers.len()).to_be_greater_than(0)
```

</details>

#### should reject a receipt from another run

- should reject a receipt from another run
- Review the fail-closed aggregate evidence manifest
   - Expected: aggregate_mci_evidence_v1(policy, [receipt]).matrix.result equals `MCI_EVIDENCE_BLOCKED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a receipt from another run")
step("Review the fail-closed aggregate evidence manifest")
val hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val policy = MciEvidencePolicyV1(
    schema_version: 1u16, run_id: "mci-system-run",
    source_hash: hash, configuration_hash: hash, now_utc_ns: 1000,
    required_check_ids: ["local-policy"])
var receipt = MciEvidenceReceiptV1(
    schema_version: 1u16, check_id: "local-policy",
    run_id: "another-run", source_hash: hash,
    configuration_hash: hash, valid_until_utc_ns: 1100,
    result: MCI_EVIDENCE_PASS, receipt_hash: "")
receipt.receipt_hash = mci_evidence_receipt_hash(policy, receipt)
expect(aggregate_mci_evidence_v1(policy, [receipt]).matrix.result).to_equal(MCI_EVIDENCE_BLOCKED)
```

</details>

#### should reject expired evidence

- should reject expired evidence
- Review the fail-closed aggregate evidence manifest
   - Expected: aggregate_mci_evidence_v1(policy, [receipt]).matrix.result equals `MCI_EVIDENCE_BLOCKED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject expired evidence")
step("Review the fail-closed aggregate evidence manifest")
val hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val policy = MciEvidencePolicyV1(
    schema_version: 1u16, run_id: "mci-system-run",
    source_hash: hash, configuration_hash: hash, now_utc_ns: 1000,
    required_check_ids: ["local-policy"])
var receipt = MciEvidenceReceiptV1(
    schema_version: 1u16, check_id: "local-policy",
    run_id: "mci-system-run", source_hash: hash,
    configuration_hash: hash, valid_until_utc_ns: 999,
    result: MCI_EVIDENCE_PASS, receipt_hash: "")
receipt.receipt_hash = mci_evidence_receipt_hash(policy, receipt)
expect(aggregate_mci_evidence_v1(policy, [receipt]).matrix.result).to_equal(MCI_EVIDENCE_BLOCKED)
```

</details>

#### should admit exact-current compiler evidence and reject stale lineage

- should admit exact-current compiler evidence and reject stale lineage
- Prepare an isolated mission-critical evidence run
- Admit exact-current compiler and tooling artifacts
   - Expected: if run.is_valid(): 101 else: -101 equals `101`
   - Expected: if run_compiler_admission(run, artifact, fixture).is_admitted(): 102 else: -102 equals `102`
   - Expected: run_compiler_admission(run, stale, fixture).rejection.name() equals `stale_lineage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should admit exact-current compiler evidence and reject stale lineage")
step("Prepare an isolated mission-critical evidence run")
val hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val expected_fixture = MciExpectedFixtureV2(
    fixture_id: "discriminating-emission", command_hash: hash,
    timeout_ms: 2000, expected_exit_code: 0,
    expected_capture_hash: hash, expected_artifact_hash: hash,
    expected_emitted_function_count: 3)
var run = MciRunIdentityV1(
    schema_version: "mci-compiler-admission-run-v2",
    run_id: "mci-system-run", source_hash: hash, config_hash: hash,
    toolchain_hash: hash, dependency_hash: hash, environment_hash: hash,
    input_bundle_hash: hash, expected_receipt_hash: hash,
    expected_parent_artifact_id: "simple-parent",
    expected_parent_source_hash: hash,
    expected_parent_executable_hash: hash,
    expected_parent_receipt_hash: hash,
    expected_fixtures: [expected_fixture])

step("Admit exact-current compiler and tooling artifacts")
val artifact = MciArtifactIdentityV1(
    schema_version: "mci-compiler-artifact-v2",
    artifact_id: "simple-current", lineage: MciCompilerLineageV1.PureSimple,
    compiler_source_hash: hash, executable_path_hash: hash,
    executable_hash: hash, input_bundle_hash: hash,
    parent: MciParentLineageEvidenceV2(
        lineage: MciCompilerLineageV1.PureSimple,
        parent_artifact_id: "simple-parent", parent_source_hash: hash,
        parent_executable_hash: hash, parent_receipt_hash: hash))
var fixture = MciGateReceiptV1(
    schema_version: "mci-compiler-collector-receipt-v2",
    collector_id: "pure-collector-v2", run_id: "mci-system-run",
    receipt_hash: hash, input_bundle_hash: hash, source_hash: hash,
    config_hash: hash, toolchain_hash: hash, dependency_hash: hash,
    environment_hash: hash, resolved_executable_path_hash: hash,
    compiler_executable_hash: hash, parent_receipt_hash: hash,
    fixtures: [MciFixtureReceiptV2(
        fixture_id: "discriminating-emission", command_hash: hash,
        timeout_ms: 2000, exit_code: 0, capture_hash: hash,
        emitted_artifact_hash: hash, resolved_executable_path_hash: hash,
        compiler_executable_hash: hash, emitted_function_count: 3)])
fixture.receipt_hash = mci_compiler_receipt_hash(fixture)
run.expected_receipt_hash = fixture.receipt_hash
# Distinct diagnostic codes keep this umbrella flow actionable even on
# runners that omit assertion source locations.
expect(if run.is_valid(): 101 else: -101).to_equal(101)
expect(if run_compiler_admission(run, artifact, fixture).is_admitted(): 102 else: -102).to_equal(102)
var stale = artifact
stale.lineage = MciCompilerLineageV1.Stale
expect(run_compiler_admission(run, stale, fixture).rejection.name()).to_equal("stale_lineage")
```

</details>

#### should enforce bounded OS rendering allocation and process policies

- should enforce bounded OS rendering allocation and process policies
- Exercise the certified SimpleOS platform manifest
   - Expected: subset.status equals `pass`
   - Expected: subset.selected_cell_count equals `2u32`
   - Expected: subset.visible_cell_count equals `24u32`
   - Expected: if not subset.umbrella_all_platforms: 201 else: -201 equals `201`
   - Expected: certified_simpleos_manifest_validate(wrong_host).reason equals `receipt-correlation-mismatch:linux:x86_32`
- Exercise packed rendering and backend provenance
   - Expected: admitted.arena_id equals `41u64`
   - Expected: admitted.generation equals `1u64`
   - Expected: admitted.total_bytes equals `64u64`
   - Expected: if draw_arena.retire(): 301 else: -301 equals `301`
   - Expected: receipt.reason equals `DRAW_IR_OVERFLOW_COUNT`
- Exercise strict and relaxed allocation profiles
   - Expected: reference.size_bytes equals `64u64`
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_QUOTA`
   - Expected: if domain_arena.rollback(checkpoint): 401 else: -401 equals `401`
   - Expected: domain_arena.cursor_bytes equals `0u64`
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_FORBIDDEN_CONTEXT`
   - Expected: if domain_arena.rollback(forbidden_checkpoint): 402 else: -402 equals `402`
- Exercise bounded concurrency and process failure paths
   - Expected: if not validate_process_signal_pid(-1).accepted: 501 else: -501 equals `501`
   - Expected: if not validate_process_signal_pid(0).accepted: 502 else: -502 equals `502`
   - Expected: if not saturated_work.accepted: 503 else: -503 equals `503`
   - Expected: if exact_capture.accepted: 504 else: -504 equals `504`
   - Expected: if not overflow_capture.accepted: 505 else: -505 equals `505`
   - Expected: if slot.accepted: 506 else: -506 equals `506`
   - Expected: timeout.after equals `BoundedExecutionStateV4.TerminationRequested`
   - Expected: if timeout.terminate_group_intent: 507 else: -507 equals `507`
- Verify freshness, bounds, isolation, and performance budgets
   - Expected: draw_arena.next_generation equals `2u64`
   - Expected: domain_arena.committed_generation equals `0u64`
   - Expected: domain_arena.next_generation equals `3u64`
   - Expected: domain_arena.high_water_bytes equals `64u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 103 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enforce bounded OS rendering allocation and process policies")
step("Exercise the certified SimpleOS platform manifest")
val subset = certified_simpleos_manifest_validate(mci_subset_manifest())
expect(subset.status).to_equal("pass")
expect(subset.selected_cell_count).to_equal(2u32)
expect(subset.visible_cell_count).to_equal(24u32)
expect(if not subset.umbrella_all_platforms: 201 else: -201).to_equal(201)
var wrong_host = mci_subset_manifest()
var wrong_host_row = wrong_host.cells[0]
var wrong_host_boot = wrong_host_row.boot
wrong_host_boot.host_identity = "host-windows"
wrong_host_row.boot = wrong_host_boot
wrong_host.cells[0] = wrong_host_row
wrong_host.manifest_hash = certified_simpleos_manifest_hash_v1(wrong_host)
expect(certified_simpleos_manifest_validate(wrong_host).reason).to_equal("receipt-correlation-mismatch:linux:x86_32")

step("Exercise packed rendering and backend provenance")
val exact_counts = draw_ir_generation_count_v3(
    2u32, 1u32, 1u32, 1u32, 1u32, 2u32)
val exact_plan = draw_ir_generation_plan_v3(
    41u64, 1u64, exact_counts, 8u64, 64u64, 8u64)
var draw_arena = DrawIrGenerationArenaV3.bounded(41u64, 64u64, 8u64)
match exact_plan:
    DrawIrPlanOutcomeV3.Planned(plan):
        match draw_arena.admit(plan):
            DrawIrAdmissionOutcomeV3.Admitted(admitted):
                expect(admitted.arena_id).to_equal(41u64)
                expect(admitted.generation).to_equal(1u64)
                expect(admitted.total_bytes).to_equal(64u64)
            DrawIrAdmissionOutcomeV3.Refused(receipt):
                fail("unexpected Draw IR admission refusal")
    DrawIrPlanOutcomeV3.Refused(receipt):
        fail("unexpected Draw IR planning refusal")
expect(draw_arena.seal(64u64, 8u64)).to_be_nil()
expect(if draw_arena.retire(): 301 else: -301).to_equal(301)
val plus_one = draw_ir_generation_plan_v3(
    41u64, 2u64,
    draw_ir_generation_count_v3(9u32, 0u32, 0u32, 0u32, 0u32, 0u32),
    8u64, 64u64, 8u64)
match plus_one:
    DrawIrPlanOutcomeV3.Refused(receipt):
        expect(receipt.reason).to_equal(DRAW_IR_OVERFLOW_COUNT)
    DrawIrPlanOutcomeV3.Planned(plan):
        fail("Draw IR overflow was clamped instead of refused")

step("Exercise strict and relaxed allocation profiles")
var domain_arena = DomainArenaV1.from_sealed_profile(51u64, mci_relaxed_profile())
val checkpoint = domain_arena.checkpoint()
match domain_arena.try_allocate(64u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Allocated(reference):
        expect(reference.size_bytes).to_equal(64u64)
    DomainArenaAllocationV1.Exhausted(receipt):
        fail("unexpected exact-quota allocation exhaustion")
match domain_arena.try_allocate(1u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_QUOTA)
    DomainArenaAllocationV1.Allocated(reference):
        fail("quota overflow allocation was unexpectedly admitted")
expect(if domain_arena.rollback(checkpoint): 401 else: -401).to_equal(401)
expect(domain_arena.cursor_bytes).to_equal(0u64)
val forbidden_checkpoint = domain_arena.checkpoint()
match domain_arena.try_allocate(8u64, ARENA_CONTEXT_ISR):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_FORBIDDEN_CONTEXT)
    DomainArenaAllocationV1.Allocated(reference):
        fail("forbidden-context allocation was unexpectedly admitted")
expect(if domain_arena.rollback(forbidden_checkpoint): 402 else: -402).to_equal(402)

step("Exercise bounded concurrency and process failure paths")
expect(if not validate_process_signal_pid(-1).accepted: 501 else: -501).to_equal(501)
expect(if not validate_process_signal_pid(0).accepted: 502 else: -502).to_equal(502)
val saturated_work = admit_bounded_work(BoundedWorkPoolV1(
    max_workers: 2, max_pending: 1,
    active_workers: 2, pending_work: 1))
expect(if not saturated_work.accepted: 503 else: -503).to_equal(503)
val exact_capture = admit_bounded_capture(BoundedProcessCaptureV1(
    max_stdout_bytes: 16, max_stderr_bytes: 8,
    stdout_bytes: 16, stderr_bytes: 8))
expect(if exact_capture.accepted: 504 else: -504).to_equal(504)
val overflow_capture = admit_bounded_capture(BoundedProcessCaptureV1(
    max_stdout_bytes: 16, max_stderr_bytes: 8,
    stdout_bytes: 17, stderr_bytes: 8))
expect(if not overflow_capture.accepted: 505 else: -505).to_equal(505)
val slot = reserve_process_slot_v4(ProcessSlotPoolV4(
    max_in_flight: 2, reserved: 1, generation: 9))
expect(if slot.accepted: 506 else: -506).to_equal(506)
val lease_hash = process_owner_lease_token_v4(1, 2, 3, 4, 71, 71, slot.slot_token)
val lease = ProcessOwnerLeaseV4(run_id: 1, execution_id: 2, generation: 3,
    start_identity: 4, pid: 71, process_group_id: 71,
    admission_slot_token: slot.slot_token, lease_token: lease_hash)
val execution = BoundedExecutionV4(
    state: BoundedExecutionStateV4.Running, lease: lease, transition_sequence: 0)
val timeout = transition_bounded_execution_v4(
    execution, BoundedExecutionEventV4.ReachTimeout, lease, 0)
expect(timeout.after).to_equal(BoundedExecutionStateV4.TerminationRequested)
expect(if timeout.terminate_group_intent: 507 else: -507).to_equal(507)

step("Verify freshness, bounds, isolation, and performance budgets")
expect(draw_arena.next_generation).to_equal(2u64)
expect(domain_arena.committed_generation).to_equal(0u64)
expect(domain_arena.next_generation).to_equal(3u64)
expect(domain_arena.high_water_bytes).to_equal(64u64)
```

</details>

#### should keep absent external evidence fail-closed

- should keep absent external evidence fail-closed
- Review the fail-closed aggregate evidence manifest
   - Expected: aggregate.matrix.result equals `MCI_EVIDENCE_BLOCKED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep absent external evidence fail-closed")
step("Review the fail-closed aggregate evidence manifest")
val hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val policy = MciEvidencePolicyV1(
    schema_version: 1u16, run_id: "mci-system-run",
    source_hash: hash, configuration_hash: hash, now_utc_ns: 1000,
    required_check_ids: ["local-policy", "external-host-tooling"]
)
var local_receipt = MciEvidenceReceiptV1(
    schema_version: 1u16, check_id: "local-policy",
    run_id: "mci-system-run", source_hash: hash,
    configuration_hash: hash, valid_until_utc_ns: 1100,
    result: MCI_EVIDENCE_PASS, receipt_hash: ""
)
local_receipt.receipt_hash = mci_evidence_receipt_hash(policy, local_receipt)
val aggregate = aggregate_mci_evidence_v1(policy, [local_receipt])
expect(aggregate.matrix.result).to_equal(MCI_EVIDENCE_BLOCKED)
expect(aggregate.matrix.blockers.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-MCI-003`
- `REQ-MCI-004`
- `REQ-MCI-005`
- `REQ-MCI-007`
- `REQ-MCI-008`
- `REQ-MCI-010`
- `REQ-MCI-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d04c77afe3c700a17ae8b10daf9cdc079b2f54cf13fd62c154b9f20fb62a431a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d04c77afe3c700a17ae8b10daf9cdc079b2f54cf13fd62c154b9f20fb62a431a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d04c77afe3c700a17ae8b10daf9cdc079b2f54cf13fd62c154b9f20fb62a431a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl
mirror: doc/06_spec/03_system/infra/mission_critical_infra_hardening_v2_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/infra/mission_critical_infra_hardening_v2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/infra/mission_critical_infra_hardening_v2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl:167:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit a selected certified guest subset' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should admit a selected certified guest subset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl:176:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain unselected platform rows without an umbrella claim' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl:176:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain unselected platform rows without an umbrella claim' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl:184:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a guest receipt with mismatched host identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a guest receipt with mismatched host identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl:198:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit an exactly sized packed generation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl:216:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should seal and retire a published generation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl:235:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should refuse row overflow before admission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
