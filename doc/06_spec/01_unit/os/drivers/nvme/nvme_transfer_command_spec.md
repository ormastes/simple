# Nvme Transfer Command Specification

> <details>

<!-- sdn-diagram:id=nvme_transfer_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_transfer_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_transfer_command_spec -> std
nvme_transfer_command_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_transfer_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Transfer Command Specification

## Scenarios

### NVMe transfer command

#### builds read and write commands without syscall or C bridge state

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val read = nvme_read_io_command(0x100000002u64, 8u32, 0x200000u64, 0x100000100u64).unwrap()
expect(read.opcode).to_equal(NVME_TRANSFER_OPCODE_READ)
expect(read.nsid).to_equal(1u32)
expect(read.prp1).to_equal(0x200000u64)
expect(read.cdw10).to_equal(2u32)
expect(read.cdw11).to_equal(1u32)
expect(read.cdw12).to_equal(7u32)

val write = nvme_write_io_command(4u64, 1u32, 0x300000u64, 16u64).unwrap()
expect(write.opcode).to_equal(NVME_TRANSFER_OPCODE_WRITE)
expect(write.cdw12).to_equal(0u32)
```

</details>

#### builds namespace-aware read and write commands for assigned namespaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val read = nvme_read_io_command_for_namespace(7u32, 4u64, 2u32, 0x200000u64, 16u64).unwrap()
expect(read.opcode).to_equal(NVME_TRANSFER_OPCODE_READ)
expect(read.nsid).to_equal(7u32)
expect(read.cdw12).to_equal(1u32)

val write = nvme_write_io_command_for_namespace(9u32, 8u64, 1u32, 0x300000u64, 16u64).unwrap()
expect(write.opcode).to_equal(NVME_TRANSFER_OPCODE_WRITE)
expect(write.nsid).to_equal(9u32)
expect(write.cdw12).to_equal(0u32)
```

</details>

#### rejects unsafe ranges before command submission

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nvme_read_io_command_for_namespace(0u32, 0u64, 1u32, 0x200000u64, 16u64).unwrap_err()).to_equal("nvme-io-namespace-zero")
expect(nvme_io_lba_range_reason(0u64, 0u32, 16u64)).to_equal("nvme-io-zero-sector-count")
expect(nvme_io_lba_range_reason(0u64, 65537u32, 70000u64)).to_equal("nvme-io-sector-count-too-large")
expect(nvme_io_lba_range_reason(15u64, 2u32, 16u64)).to_equal("nvme-io-beyond-namespace-capacity")
expect(nvme_read_io_command(0u64, 1u32, 0u64, 16u64).unwrap_err()).to_equal("nvme-io-dma-buffer-zero")
```

</details>

#### shares flush command and completion status decoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flush = nvme_flush_io_command()
expect(flush.opcode).to_equal(0u8)
expect(flush.nsid).to_equal(1u32)
val ns_flush = nvme_flush_io_command_for_namespace(7u32).unwrap()
expect(ns_flush.opcode).to_equal(0u8)
expect(ns_flush.nsid).to_equal(7u32)
expect(nvme_flush_io_command_for_namespace(0u32).unwrap_err()).to_equal("nvme-io-namespace-zero")
expect(nvme_io_status_code(0u32)).to_equal(0u32)
expect(nvme_io_status_code(4u32 << 17)).to_equal(4u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_transfer_command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe transfer command

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
