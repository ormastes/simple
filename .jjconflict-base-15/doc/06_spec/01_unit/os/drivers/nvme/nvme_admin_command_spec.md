# Nvme Admin Command Specification

> <details>

<!-- sdn-diagram:id=nvme_admin_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_admin_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_admin_command_spec -> std
nvme_admin_command_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_admin_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Admin Command Specification

## Scenarios

### NVMe admin command

#### builds identify commands without hosted driver state

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = nvme_admin_identify_controller(0x200000u64).unwrap()
expect(controller.opcode).to_equal(NVME_ADMIN_IDENTIFY)
expect(controller.nsid).to_equal(0u32)
expect(controller.prp1).to_equal(0x200000u64)
expect(controller.cdw10).to_equal(1u32)

val namespace_cmd = nvme_admin_identify_namespace(1u32, 0x210000u64).unwrap()
expect(namespace_cmd.opcode).to_equal(NVME_ADMIN_IDENTIFY)
expect(namespace_cmd.nsid).to_equal(1u32)
expect(namespace_cmd.prp1).to_equal(0x210000u64)
expect(namespace_cmd.cdw10).to_equal(0u32)
```

</details>

#### builds queue feature and create queue commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queues = nvme_admin_set_num_queues(2u16, 3u16).unwrap()
expect(queues.opcode).to_equal(NVME_ADMIN_SET_FEATURES)
expect(queues.cdw10).to_equal(0x07u32)
expect(queues.cdw11).to_equal(1u32 | (2u32 << 16))

val iocq = nvme_admin_create_io_completion_queue(1u16, 64u16, 0x300000u64).unwrap()
expect(iocq.opcode).to_equal(NVME_ADMIN_CREATE_IOCQ)
expect(iocq.prp1).to_equal(0x300000u64)
expect(iocq.cdw10).to_equal(1u32 | (63u32 << 16))
expect(iocq.cdw11).to_equal(1u32)

val iosq = nvme_admin_create_io_submission_queue(1u16, 64u16, 1u16, 0x310000u64).unwrap()
expect(iosq.opcode).to_equal(NVME_ADMIN_CREATE_IOSQ)
expect(iosq.prp1).to_equal(0x310000u64)
expect(iosq.cdw10).to_equal(1u32 | (63u32 << 16))
expect(iosq.cdw11).to_equal(1u32 | (1u32 << 16))
```

</details>

#### rejects invalid admin command resources before submission

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nvme_admin_identify_controller(0u64).unwrap_err()).to_equal("nvme-admin-identify-buffer-zero")
expect(nvme_admin_identify_namespace(0u32, 0x200000u64).unwrap_err()).to_equal("nvme-admin-identify-namespace-zero")
expect(nvme_admin_set_num_queues(0u16, 1u16).unwrap_err()).to_equal("nvme-admin-queue-count-zero")
expect(nvme_admin_create_io_completion_queue(0u16, 64u16, 0x300000u64).unwrap_err()).to_equal("nvme-admin-iocq-qid-zero")
expect(nvme_admin_create_io_submission_queue(1u16, 64u16, 0u16, 0x310000u64).unwrap_err()).to_equal("nvme-admin-iosq-cqid-zero")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_admin_command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe admin command

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
