# task_policy_attr_spec

> Unit tests for @task scheduler policy validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# task_policy_attr_spec

Unit tests for @task scheduler policy validation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/common/task_policy_attr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for @task scheduler policy validation.

## Scenarios

### Task scheduler policy attributes

#### allows fair policy in hosted async runtime

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows fair policy in hosted async runtime
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows fair policy in hosted async runtime")
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

#### rejects rt policy outside noalloc runtime

- rejects rt policy outside noalloc runtime
   - Expected: result.has_errors is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects rt policy outside noalloc runtime")
val attr = TaskAttr(
    instances: 1,
    group: nil,
    frame: nil,
    wait_nodes: 0,
    policy: "rt_rr",
    weight: nil,
    priority: 48,
    latency_hint: nil,
    runtime_ns: nil,
    period_ns: nil,
    deadline_ns: nil
)
val result = validate_task_policy_attr(attr, "nogc_async_mut", [])
expect(result.has_errors).to_equal(true)
```

</details>

#### allows admitted deadline policy in noalloc runtime

- allows admitted deadline policy in noalloc runtime
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows admitted deadline policy in noalloc runtime")
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

#### rejects deadline policy with invalid budget tuple

- rejects deadline policy with invalid budget tuple
   - Expected: result.has_errors is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects deadline policy with invalid budget tuple")
val attr = TaskAttr(
    instances: 1,
    group: nil,
    frame: nil,
    wait_nodes: 0,
    policy: "deadline",
    weight: nil,
    priority: nil,
    latency_hint: nil,
    runtime_ns: 800000,
    period_ns: 1000000,
    deadline_ns: 400000
)
val result = validate_task_policy_attr(attr, "nogc_async_mut_noalloc", [])
expect(result.has_errors).to_equal(true)
```

</details>

#### rejects deadline policy with allocation effects

- rejects deadline policy with allocation effects
   - Expected: result.has_errors is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects deadline policy with allocation effects")
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
val result = validate_task_policy_attr(attr, "nogc_async_mut_noalloc", ["alloc"])
expect(result.has_errors).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a94e73ce4f86e828459b0f17e0d67c89969e2c5b15ef61981d0c962c9e998a02`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a94e73ce4f86e828459b0f17e0d67c89969e2c5b15ef61981d0c962c9e998a02`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a94e73ce4f86e828459b0f17e0d67c89969e2c5b15ef61981d0c962c9e998a02`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/common/task_policy_attr_spec.spl
mirror: doc/06_spec/unit/compiler/common/task_policy_attr_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/common/task_policy_attr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/common/task_policy_attr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/common/task_policy_attr_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows fair policy in hosted async runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/task_policy_attr_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects rt policy outside noalloc runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/task_policy_attr_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows admitted deadline policy in noalloc runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
