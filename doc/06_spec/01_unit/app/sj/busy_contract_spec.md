# BUSY Contract Specification

> <details>

<!-- sdn-diagram:id=busy_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=busy_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

busy_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=busy_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BUSY Contract Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sj/busy_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### BUSY Contract - Exit Code

#### BUSY result indicates failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
expect(second.ok).to_equal(false)
val msg = second.busy_message
expect(msg).to_contain("BUSY")
```

</details>

#### BUSY message is not empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
val msg = second.busy_message
expect(msg.len()).to_be_greater_than(0i64)
```

</details>

### BUSY Contract - JSON Wire Format

#### formats BUSY JSON with error field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = format_busy_json("lease-1", 12345i64, "2026-01-01T00:00:30Z")
expect(json).to_contain("\"error\":\"BUSY\"")
expect(json).to_contain("\"lease_id\":\"lease-1\"")
expect(json).to_contain("\"holder_pid\":12345")
```

</details>

### BUSY Contract - Exit 0 Regression

#### successful lease does not produce BUSY

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val result = try_acquire_exclusive(mgr, pid, 30000i64)
expect(result.ok).to_equal(true)
val msg = result.busy_message
expect(msg).to_equal("")
```

</details>

#### released lease allows next acquire

1. release lease
   - Expected: second.ok is true
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
release_lease(mgr, first.lease_id)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
expect(second.ok).to_equal(true)
val msg = second.busy_message
expect(msg).to_equal("")
```

</details>

### BUSY Contract - Lease ID in Message

#### BUSY message contains BUSY keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
val msg = second.busy_message
expect(msg).to_contain("BUSY")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
