# scheduler_process_isolation_spec

> System-facing scheduler process isolation specification.

<!-- sdn-diagram:id=scheduler_process_isolation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scheduler_process_isolation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scheduler_process_isolation_spec -> std
scheduler_process_isolation_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scheduler_process_isolation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

System-facing scheduler process isolation specification.

## Scenarios

### scheduler_process_isolation

### REQ-SPI-006: task policy validation

#### allows fair tasks in hosted runtime families

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

#### rejects realtime task metadata outside noalloc runtime

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

#### rejects deadline task metadata with invalid budget

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
