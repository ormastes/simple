# Test Daemon Resource Policy Specification

> <details>

<!-- sdn-diagram:id=test_daemon_resource_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_resource_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_resource_policy_spec -> std
test_daemon_resource_policy_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_resource_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Daemon Resource Policy Specification

## Scenarios

### TestDaemonResourcePolicy

<details>
<summary>Advanced: accepts clients when the host has resource headroom</summary>

#### accepts clients when the host has resource headroom

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = test_daemon_can_accept_client(policy(), snap(40.0, 50.0, 1, 0, 0, 8, 16384))
expect(ok[0]).to_equal(true)
expect(ok[1]).to_equal("")
```

</details>


</details>

#### queues clients when max client slots are already active

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = test_daemon_can_accept_client(policy(), snap(10.0, 10.0, 4, 0, 0, 8, 16384))
expect(ok[0]).to_equal(false)
expect(ok[1]).to_contain("client limit")
```

</details>

#### queues clients when free memory is below the safety floor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = test_daemon_can_accept_client(policy(), snap(10.0, 90.0, 0, 0, 0, 8, 16384))
expect(ok[0]).to_equal(false)
expect(ok[1]).to_contain("memory")
```

</details>

#### computes QEMU limit from configured max, CPU budget, and memory budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limit = test_daemon_effective_qemu_limit(policy(), snap(10.0, 10.0, 0, 0, 0, 2, 4096))
expect(limit).to_equal(1)
```

</details>

#### queues QEMU when active sessions reach the effective limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = test_daemon_can_start_qemu(policy(), snap(10.0, 10.0, 0, 1, 0, 2, 4096))
expect(ok[0]).to_equal(false)
expect(ok[1]).to_contain("qemu")
```

</details>

#### uses long sleep while idle and short sleep while busy

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = policy()
val idle = test_daemon_poll_sleep_ms(p, snap(5.0, 5.0, 0, 0, 0, 8, 16384), 0)
val busy = test_daemon_poll_sleep_ms(p, snap(5.0, 5.0, 1, 0, 0, 8, 16384), 0)
expect(idle).to_equal(1000)
expect(busy).to_equal(100)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_resource_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestDaemonResourcePolicy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
