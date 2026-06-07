# task_policy_attr_spec

> Unit tests for @task scheduler policy validation.

<!-- sdn-diagram:id=task_policy_attr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=task_policy_attr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

task_policy_attr_spec -> std
task_policy_attr_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=task_policy_attr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/compiler/common/task_policy_attr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for @task scheduler policy validation.

## Scenarios

### Task scheduler policy attributes

#### allows fair policy in hosted async runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
