# scheduler_process_isolation_spec

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scheduler_process_isolation_spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/scheduler_process_isolation_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

## Scenarios

### scheduler_process_isolation

### REQ-SPI-006: task policy validation

#### allows fair tasks in hosted runtime families

- Verify: allows fair tasks in hosted runtime families
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPI-006
step("Verify: allows fair tasks in hosted runtime families")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val attr = TaskAttr(
    instances: 1,
    group: nil,
    frame: nil,
    wait_nodes: 0,
    policy: "fair",
    weight: nil,
    priority: nil,
    latency_hint: nil,
    runtime_ns: nil,
    period_ns: nil,
    deadline_ns: nil
)
val result = validate_task_policy_attr(attr, "nogc_async_mut", [])
expect(result.has_errors).to_equal(false)
```

</details>

#### rejects realtime task metadata outside noalloc runtime

- Verify: rejects realtime task metadata outside noalloc runtime
   - Expected: result.has_errors is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPI-006
step("Verify: rejects realtime task metadata outside noalloc runtime")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: allows deadline task metadata with valid noalloc budget
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPI-006
step("Verify: allows deadline task metadata with valid noalloc budget")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects deadline task metadata with invalid budget
   - Expected: result.has_errors is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SPI-006
step("Verify: rejects deadline task metadata with invalid budget")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `743124b96a380b74b860a09a80fd4bd56b22ea66194cece354f516cd1a8cfc9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `743124b96a380b74b860a09a80fd4bd56b22ea66194cece354f516cd1a8cfc9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `743124b96a380b74b860a09a80fd4bd56b22ea66194cece354f516cd1a8cfc9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/compiler/feature/scheduler_process_isolation_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/scheduler_process_isolation_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/compiler/feature/scheduler_process_isolation_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/compiler/feature/scheduler_process_isolation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/scheduler_process_isolation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
