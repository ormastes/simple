# Hwir Aspect Lock Specification

> Tests covering content-addressed Gen2 hardware aspect locks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Aspect Lock Specification

## Scenarios

### content-addressed Gen2 hardware aspect locks

#### should pin the exact planned manifest identity and reject hash drift

- should pin the exact planned manifest identity and reject hash drift
- Create the planned manifest lock and compare it with a changed content hash
   - Expected: lock_result.is_ok() is true
   - Expected: lock.entries.len() equals `1`
   - Expected: hwir_aspect_plan_lock_diagnostic(plan, lock) equals ``
   - Expected: hwir_aspect_plan_lock_diagnostic(plan, changed) equals `HWIR-E-ASPECT-LOCK: aspect lock does not pin the planned manifest identity`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should pin the exact planned manifest identity and reject hash drift")
step("Create the planned manifest lock and compare it with a changed content hash")
var manifest = locked_aspect_manifest()
manifest.required = false
val plan = HwAspectPlan(manifests: [manifest], applications: [])
val lock_result = hwir_aspect_lock_for_plan(plan)
expect(lock_result.is_ok()).to_equal(true)
if lock_result.is_ok():
    val lock = lock_result.ok().unwrap()
    expect(lock.entries.len()).to_equal(1)
    expect(hwir_aspect_plan_lock_diagnostic(plan, lock)).to_equal("")
    val changed = HwAspectLock(entries: [HwAspectLockEntry(id: "debug.rvfi",
        version: "1.0.0",
        content_hash: "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")])
    expect(hwir_aspect_plan_lock_diagnostic(plan, changed)).to_equal("HWIR-E-ASPECT-LOCK: aspect lock does not pin the planned manifest identity")
else:
    expect(false).to_equal(true)
```

</details>

#### should weave an observational port only under its exact content-addressed lock

- should weave an observational port only under its exact content-addressed lock
- Lower a typed module and weave its declared observational probe through the matching lock
   - Expected: result.is_ok() is true
   - Expected: result.ok().unwrap().added_port_count equals `1`
   - Expected: false is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should weave an observational port only under its exact content-addressed lock")
step("Lower a typed module and weave its declared observational probe through the matching lock")
val lowered = lower_strict_hwir_and_module(
    HwirLowerInput.hardware("locked_aspect_and", 2, 1, 0, 0), CoreConfig.rv32())
if lowered.module != nil:
    val module = lowered.module.unwrap()
    val manifest = locked_aspect_manifest()
    val plan = HwAspectPlan(manifests: [manifest], applications: [
        HwAspectApplication(aspect_id: "debug.rvfi", matched_node_ids: [module.node_id], woven_node_count: 1)
    ])
    val lock_result = hwir_aspect_lock_for_plan(plan)
    if lock_result.is_ok():
        val result = weave_hwir_observational_ports_locked(module, plan, lock_result.ok().unwrap(), [
            HwAspectProbe(aspect_id: "debug.rvfi", target_node_id: module.node_id,
                source_value: "in_a", output_port: "rvfi_in_a")
        ])
        expect(result.is_ok()).to_equal(true)
        if result.is_ok():
            expect(result.ok().unwrap().added_port_count).to_equal(1)
        else:
            expect(false).to_equal(true)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should fail closed for an incomplete lock before graph mutation

- should fail closed for an incomplete lock before graph mutation
- Present an empty lock for a plan that declares one manifest
   - Expected: hwir_aspect_plan_lock_diagnostic(plan, empty_lock) equals `HWIR-E-ASPECT-LOCK: aspect lock must contain exactly the planned manifests`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should fail closed for an incomplete lock before graph mutation")
step("Present an empty lock for a plan that declares one manifest")
var manifest = locked_aspect_manifest()
manifest.required = false
val plan = HwAspectPlan(manifests: [manifest], applications: [])
val empty_lock = HwAspectLock(entries: [])
expect(hwir_aspect_plan_lock_diagnostic(plan, empty_lock)).to_equal("HWIR-E-ASPECT-LOCK: aspect lock must contain exactly the planned manifests")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_aspect_lock_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering content-addressed Gen2 hardware aspect locks.
- content-addressed Gen2 hardware aspect locks

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

- Canonical SPipe generation for source `e5a2e4924681f9a550823dae2ad8075372eac7be45ddc90abf2a407fd1c5dde9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5a2e4924681f9a550823dae2ad8075372eac7be45ddc90abf2a407fd1c5dde9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5a2e4924681f9a550823dae2ad8075372eac7be45ddc90abf2a407fd1c5dde9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/50.mir/hwir_aspect_lock_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_aspect_lock_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_aspect_lock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_aspect_lock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_aspect_lock_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_aspect_lock_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pin the exact planned manifest identity and reject hash drift' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_aspect_lock_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pin the exact planned manifest identity and reject hash drift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_aspect_lock_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should weave an observational port only under its exact content-addressed lock' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_aspect_lock_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should weave an observational port only under its exact content-addressed lock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_aspect_lock_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed for an incomplete lock before graph mutation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_aspect_lock_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed for an incomplete lock before graph mutation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
