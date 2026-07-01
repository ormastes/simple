# Vfs Boot Production Handoff Specification

> <details>

<!-- sdn-diagram:id=vfs_boot_production_handoff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vfs_boot_production_handoff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vfs_boot_production_handoff_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vfs_boot_production_handoff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vfs Boot Production Handoff Specification

## Scenarios

### VFS production NVMe boot handoff

#### provisions the freestanding production mount from the real pure NVMe path

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/os/services/vfs/vfs_boot_init.spl")
val pure_pos = source.index_of("fn _vfs_boot_init_pure_nvme_fat32")
val virtio_pos = source.index_of("fn _vfs_boot_init_virtio_fat32")
val pure_body = source.substring(pure_pos, virtio_pos)
val evidence_pos = pure_body.index_of("val transfer_evidence = transfer_evidence_result.unwrap()")
val lease_pos = pure_body.index_of("val lease = lease_result.unwrap()")
val adapter_pos = pure_body.index_of("g_adapter = adapter_result.unwrap()")
val bounce_pos = pure_body.index_of("val bounce_init = g_adapter.init_bounce_buffer()")
val provision_pos = pure_body.index_of("boot_nvme_production_handoff_provision(g_adapter, transfer_evidence, lease)")
val fat_mount_pos = pure_body.index_of("var root = Fat32Core.new(g_adapter)")

expect(source.index_of("boot_nvme_production_handoff_provision") >= 0).to_equal(true)
expect(evidence_pos >= 0).to_equal(true)
expect(lease_pos > evidence_pos).to_equal(true)
expect(adapter_pos > lease_pos).to_equal(true)
expect(bounce_pos > adapter_pos).to_equal(true)
expect(provision_pos > bounce_pos).to_equal(true)
expect(fat_mount_pos > provision_pos).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/vfs_boot_production_handoff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VFS production NVMe boot handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
