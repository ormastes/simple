# Toolchain Vfs Probe Contract Specification

> <details>

<!-- sdn-diagram:id=toolchain_vfs_probe_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=toolchain_vfs_probe_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

toolchain_vfs_probe_contract_spec -> std
toolchain_vfs_probe_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=toolchain_vfs_probe_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Toolchain Vfs Probe Contract Specification

## Scenarios

### toolchain VFS probe completion contract

#### accepts serial output with prepared scheduler task markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(toolchain_vfs_probe_serial_accepts_completion(toolchain_vfs_probe_complete_serial())).to_equal(true)
```

</details>

#### rejects serial output that lacks prepared scheduler task evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(toolchain_vfs_probe_serial_accepts_completion(toolchain_vfs_probe_without_prepared_task_marker())).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/toolchain_vfs_probe_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- toolchain VFS probe completion contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
