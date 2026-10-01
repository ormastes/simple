# scheduler_process_isolation_spec

> System-facing scheduler process isolation specification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scheduler_process_isolation_spec

System-facing scheduler process isolation specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/scheduler_process_isolation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

System-facing scheduler process isolation specification.

## Scenarios

### scheduler_process_isolation

### REQ-SPI-006: task policy validation

#### allows fair tasks in hosted runtime families
#### rejects realtime task metadata outside noalloc runtime

- rejects realtime task metadata outside noalloc runtime
   - Expected: result.has_errors is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects realtime task metadata outside noalloc runtime")
val attr = TaskAttr(
    instances: 1,
    group: nil,
    frame: nil,
    wait_nodes: 0,
    policy: "rt_rr",
    weight: nil,
    priority: nil,
    latency_hint: nil,
    runtime_ns: nil,
    period_ns: nil,
    deadline_ns: nil
)
val result = validate_task_policy_attr(attr, "nogc_async_mut", [])
expect(result.has_errors).to_equal(true)
```

</details>

#### allows deadline task metadata with valid noalloc budget

- allows deadline task metadata with valid noalloc budget
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows deadline task metadata with valid noalloc budget")
val attr = TaskAttr(
    instances: 1,
    group: nil,
    frame: nil,
    wait_nodes: 0,
    policy: "deadline",
    weight: nil,
    priority: nil,
    latency_hint: nil,
    runtime_ns: 200000,
    period_ns: 1000000,
    deadline_ns: 1000000
)
val result = validate_task_policy_attr(attr, "nogc_async_mut_noalloc", [])
expect(result.has_errors).to_equal(false)
```

</details>

#### rejects deadline task metadata with invalid budget

- rejects deadline task metadata with invalid budget
   - Expected: result.has_errors is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects deadline task metadata with invalid budget")
val attr = TaskAttr(
    instances: 1,
    group: nil,
    frame: nil,
    wait_nodes: 0,
    policy: "deadline",
    weight: nil,
    priority: nil,
    latency_hint: nil,
    runtime_ns: 1200000,
    period_ns: 1000000,
    deadline_ns: 1000000
)
val result = validate_task_policy_attr(attr, "nogc_async_mut_noalloc", [])
expect(result.has_errors).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SPI-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b0a2a108764df3e9f87cc70f35aba916a4a501850dba08fcff6829decff86db1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b0a2a108764df3e9f87cc70f35aba916a4a501850dba08fcff6829decff86db1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b0a2a108764df3e9f87cc70f35aba916a4a501850dba08fcff6829decff86db1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/compiler/feature/scheduler_process_isolation_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/scheduler_process_isolation_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=90 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/03_system/app/compiler/feature/scheduler_process_isolation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/scheduler_process_isolation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/compiler/feature/scheduler_process_isolation_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/compiler/feature/scheduler_process_isolation_spec.spl:20:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'allows fair tasks in hosted runtime families' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/compiler/feature/scheduler_process_isolation_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects realtime task metadata outside noalloc runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/scheduler_process_isolation_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows deadline task metadata with valid noalloc budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/scheduler_process_isolation_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects deadline task metadata with invalid budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
