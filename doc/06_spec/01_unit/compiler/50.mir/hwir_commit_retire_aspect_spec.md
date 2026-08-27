# Hwir Commit Retire Aspect Specification

> Tests covering typed commit.retire aspect weaving.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Commit Retire Aspect Specification

## Scenarios

### typed commit.retire aspect weaving

#### should keep an absent retirement observer structurally zero-cost

- should keep an absent retirement observer structurally zero-cost
- Build the typed retirement composition and apply the absent observer plan
   - Expected: result.is_ok() is true
   - Expected: absent.is_unchanged() is true
   - Expected: absent.route equals `hwir-aspect-absent`
   - Expected: absent.composition.node_id.value equals `composition.node_id.value`
   - Expected: absent.composition.bindings.len() equals `composition.bindings.len()`
   - Expected: absent.composition.producer.ports().len() equals `composition.producer.ports().len()`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should keep an absent retirement observer structurally zero-cost")
step("Build the typed retirement composition and apply the absent observer plan")
val built = strict_zca_single_outstanding_retirement_composition(
    "retire_aspect_absent", CoreConfig.rv32_zca_mission_critical(),
    "riscv_gen2_rv32_architectural_retirement")
if built.is_ok():
    val composition = built.ok().unwrap()
    val result = weave_hwir_commit_retire_observations_locked(composition,
        hwir_aspect_plan_absent(), HwAspectLock(entries: []), [])
    expect(result.is_ok()).to_equal(true)
    if result.is_ok():
        val absent = result.ok().unwrap()
        expect(absent.is_unchanged()).to_equal(true)
        expect(absent.route).to_equal("hwir-aspect-absent")
        expect(absent.composition.node_id.value).to_equal(composition.node_id.value)
        expect(absent.composition.bindings.len()).to_equal(composition.bindings.len())
        expect(absent.composition.producer.ports().len()).to_equal(composition.producer.ports().len())
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should weave locked typed receipt observations without changing architectural composition

- should weave locked typed receipt observations without changing architectural composition
- Lock two commit.retire observations and compare their order-independent weave receipt
   - Expected: first.is_ok() is true
   - Expected: second.is_ok() is true
   - Expected: woven.route equals `hwir-aspect-commit-retire-observe`
   - Expected: woven.added_port_count equals `2`
   - Expected: woven.weave_sha256 equals `second.ok().unwrap().weave_sha256`
   - Expected: woven.composition.bindings.len() equals `composition.bindings.len()`
   - Expected: woven.composition.producer.ports().len() equals `composition.producer.ports().len()`
   - Expected: woven.composition.shape_diagnostic() equals ``
   - Expected: false is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should weave locked typed receipt observations without changing architectural composition")
step("Lock two commit.retire observations and compare their order-independent weave receipt")
val built = strict_zca_single_outstanding_retirement_composition(
    "retire_aspect_on", CoreConfig.rv64_zca_mission_critical(),
    "riscv_gen2_rv64_architectural_retirement")
if built.is_ok():
    val composition = built.ok().unwrap()
    val node_id = hwir_commit_retire_node_id(composition)
    val plan = retire_plan(node_id, 2)
    val lock = hwir_aspect_lock_for_plan(plan)
    if lock.is_ok():
        val lineage = HwRetireObservation(aspect_id: "debug.rvfi.retire",
            target_node_id: node_id, receipt_value: "retire_lineage",
            output_port: "rvfi_retire_lineage", bit_width: 64)
        val valid = HwRetireObservation(aspect_id: "debug.rvfi.retire",
            target_node_id: node_id, receipt_value: "retire_valid",
            output_port: "rvfi_retire_valid", bit_width: 1)
        val first = weave_hwir_commit_retire_observations_locked(
            composition, plan, lock.ok().unwrap(), [lineage, valid])
        val second = weave_hwir_commit_retire_observations_locked(
            composition, plan, lock.ok().unwrap(), [valid, lineage])
        expect(first.is_ok()).to_equal(true)
        expect(second.is_ok()).to_equal(true)
        if first.is_ok() and second.is_ok():
            val woven = first.ok().unwrap()
            expect(woven.route).to_equal("hwir-aspect-commit-retire-observe")
            expect(woven.added_port_count).to_equal(2)
            expect(woven.weave_sha256).to_equal(second.ok().unwrap().weave_sha256)
            expect(woven.composition.bindings.len()).to_equal(composition.bindings.len())
            expect(woven.composition.producer.ports().len()).to_equal(composition.producer.ports().len())
            expect(woven.composition.shape_diagnostic()).to_equal("")
        else:
            expect(false).to_equal(true)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a foreign join point and a mistyped retirement field

- should reject a foreign join point and a mistyped retirement field
- Submit foreign and width-mismatched observations against the stable commit.retire node
   - Expected: foreign_result.is_err() is true
   - Expected: foreign_result.err() equals `HWIR-E-ASPECT-RETIRE-TARGET: retirement observation must bind the supplied co... (full value in folded executable source)`
   - Expected: type_result.is_err() is true
   - Expected: type_result.err() equals `HWIR-E-ASPECT-RETIRE-TYPE: retirement observation must name an exact typed pr... (full value in folded executable source)`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a foreign join point and a mistyped retirement field")
step("Submit foreign and width-mismatched observations against the stable commit.retire node")
val built = strict_zca_single_outstanding_retirement_composition(
    "retire_aspect_reject", CoreConfig.rv32_zca_mission_critical(),
    "riscv_gen2_rv32_architectural_retirement")
if built.is_ok():
    val composition = built.ok().unwrap()
    val node_id = hwir_commit_retire_node_id(composition)
    val plan = retire_plan(node_id, 1)
    val lock = hwir_aspect_lock_for_plan(plan)
    if lock.is_ok():
        val foreign = HwRetireObservation(aspect_id: "debug.rvfi.retire",
            target_node_id: HwNodeId.module_root("foreign"), receipt_value: "retire_valid",
            output_port: "rvfi_retire_valid", bit_width: 1)
        val foreign_result = weave_hwir_commit_retire_observations_locked(
            composition, plan, lock.ok().unwrap(), [foreign])
        expect(foreign_result.is_err()).to_equal(true)
        expect(foreign_result.err()).to_equal("HWIR-E-ASPECT-RETIRE-TARGET: retirement observation must bind the supplied composition's stable commit.retire node")
        val mistyped = HwRetireObservation(aspect_id: "debug.rvfi.retire",
            target_node_id: node_id, receipt_value: "retire_lineage",
            output_port: "rvfi_retire_lineage", bit_width: 32)
        val type_result = weave_hwir_commit_retire_observations_locked(
            composition, plan, lock.ok().unwrap(), [mistyped])
        expect(type_result.is_err()).to_equal(true)
        expect(type_result.err()).to_equal("HWIR-E-ASPECT-RETIRE-TYPE: retirement observation must name an exact typed producer receipt output")
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed commit.retire aspect weaving.
- typed commit.retire aspect weaving

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `230668893b2b645679c2bc5b6601922478f4b63bc05a8a64108e9dc02721893a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `230668893b2b645679c2bc5b6601922478f4b63bc05a8a64108e9dc02721893a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `230668893b2b645679c2bc5b6601922478f4b63bc05a8a64108e9dc02721893a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep an absent retirement observer structurally zero-cost' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep an absent retirement observer structurally zero-cost' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should weave locked typed receipt observations without changing architectural composition' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should weave locked typed receipt observations without changing architectural composition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.spl:104:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a foreign join point and a mistyped retirement field' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_commit_retire_aspect_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a foreign join point and a mistyped retirement field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
