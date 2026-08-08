# Concurrent Thread Lifecycle Specification

> <details>

<!-- sdn-diagram:id=concurrent_thread_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrent_thread_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrent_thread_lifecycle_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrent_thread_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrent Thread Lifecycle Specification

## Scenarios

### nogc sync thread lifecycle

#### treats repeated terminal cleanup as safe no-ops

- Spawn and join a public OS thread
   - Expected: handle.join() equals `29`
- Verify the consumed handle stays terminal
- handle free
- handle free


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Spawn and join a public OS thread")
val handle = thread_spawn(\: 29)
expect(handle.join()).to_equal(29)

step("Verify the consumed handle stays terminal")
expect(handle.is_done()).to_be(true)
expect(handle.join()).to_be_nil()
handle.free()
handle.free()
expect(handle.is_done()).to_be(true)
```

</details>

#### treats free-before-join terminal cleanup as a safe no-op

- Spawn and free a public OS thread handle before join
- handle free
- Verify the freed handle stays terminal
   - Expected: handle.join() equals `41`
- handle free
- handle free


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Spawn and free a public OS thread handle before join")
val handle = thread_spawn(\: 41)
handle.free()

step("Verify the freed handle stays terminal")
expect(handle.is_done()).to_be(true)
expect(handle.join()).to_equal(41)
handle.free()
handle.free()
expect(handle.is_done()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc sync thread lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
