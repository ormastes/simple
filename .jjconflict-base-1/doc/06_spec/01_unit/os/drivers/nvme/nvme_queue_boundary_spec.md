# Nvme Queue Boundary Specification

> <details>

<!-- sdn-diagram:id=nvme_queue_boundary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_queue_boundary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_queue_boundary_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_queue_boundary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Queue Boundary Specification

## Scenarios

### NVMe queue boundary

#### keeps reusable queue submission and polling free of hosted syscalls

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queue_source = read_file("src/os/drivers/nvme/nvme_queue.spl")
val notify_source = read_file("src/os/drivers/nvme/nvme_queue_notify.spl")

expect(queue_source.contains("extern fn syscall")).to_equal(false)
expect(queue_source.contains("NotificationWait")).to_equal(false)
expect(queue_source.contains("wait_completion_notify")).to_equal(false)

expect(notify_source.contains("extern fn syscall")).to_equal(true)
expect(notify_source.contains("wait_completion_notify")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_queue_boundary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe queue boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
