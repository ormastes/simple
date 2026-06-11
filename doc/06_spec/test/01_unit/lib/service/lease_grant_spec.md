# Lease Grant Specification

> <details>

<!-- sdn-diagram:id=lease_grant_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lease_grant_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lease_grant_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lease_grant_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lease Grant Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/service/lease_grant_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Lease Grant - Exclusive Semantics

#### grants exclusive lease when no leases are held

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val result = try_acquire_exclusive(mgr, pid, 30000i64)
expect(result.ok).to_equal(true)
val lid = result.lease_id
expect(lid.len()).to_be_greater_than(0i64)
```

</details>

#### rejects second exclusive lease while first is held

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
expect(first.ok).to_equal(true)
expect(second.ok).to_equal(false)
val msg = second.busy_message
expect(msg).to_contain("BUSY")
```

</details>

#### grants exclusive after release

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val released = release_lease(mgr, first.lease_id)
expect(released).to_equal(true)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
expect(second.ok).to_equal(true)
```

</details>

#### generates unique lease IDs

1. release lease
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
release_lease(mgr, first.lease_id)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
val fid = first.lease_id
val sid = second.lease_id
val same = fid == sid
expect(same).to_equal(false)
```

</details>

### Lease Grant - Shared Semantics

#### grants shared lease when no leases are held

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val result = try_acquire_shared(mgr, pid, 5000i64)
expect(result.ok).to_equal(true)
```

</details>

#### grants multiple shared leases concurrently

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_shared(mgr, pid, 5000i64)
val second = try_acquire_shared(mgr, pid, 5000i64)
expect(first.ok).to_equal(true)
expect(second.ok).to_equal(true)
```

</details>

#### rejects shared lease while exclusive is held

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val excl = try_acquire_exclusive(mgr, pid, 30000i64)
val shared_result = try_acquire_shared(mgr, pid, 5000i64)
expect(excl.ok).to_equal(true)
expect(shared_result.ok).to_equal(false)
val msg = shared_result.busy_message
expect(msg).to_contain("BUSY")
```

</details>

#### rejects exclusive while shared is held

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val shared_result = try_acquire_shared(mgr, pid, 5000i64)
val excl = try_acquire_exclusive(mgr, pid, 30000i64)
expect(shared_result.ok).to_equal(true)
expect(excl.ok).to_equal(false)
```

</details>

#### grants exclusive after all shared released

1. release lease
2. release lease
   - Expected: excl.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val s1 = try_acquire_shared(mgr, pid, 5000i64)
val s2 = try_acquire_shared(mgr, pid, 5000i64)
release_lease(mgr, s1.lease_id)
release_lease(mgr, s2.lease_id)
val excl = try_acquire_exclusive(mgr, pid, 30000i64)
expect(excl.ok).to_equal(true)
```

</details>

#### BUSY message contains text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = lease_manager_new()
val pid = rt_getpid()
val excl = try_acquire_exclusive(mgr, pid, 30000i64)
val shared_result = try_acquire_shared(mgr, pid, 5000i64)
val msg = shared_result.busy_message
expect(msg).to_contain("BUSY")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
