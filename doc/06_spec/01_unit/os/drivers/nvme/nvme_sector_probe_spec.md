# Nvme Sector Probe Specification

> <details>

<!-- sdn-diagram:id=nvme_sector_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_sector_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_sector_probe_spec -> std
nvme_sector_probe_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_sector_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Sector Probe Specification

## Scenarios

### NVMe sector probe

#### requires completion read write restore and shared transfer logic

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = nvme_sector_probe_result(8u64, 512u64, 0u32, true, true, true, true)
expect(nvme_sector_probe_reason(ready)).to_equal("ready")
expect(nvme_sector_probe_ready(ready)).to_equal(true)
expect(nvme_sector_probe_completion_seen(ready)).to_equal(true)

expect(nvme_sector_probe_reason(nvme_sector_probe_result(8u64, 0u64, 0u32, true, true, true, true))).to_equal("nvme-sector-probe-empty")
expect(nvme_sector_probe_reason(nvme_sector_probe_result(8u64, 512u64, 4u32, true, true, true, true))).to_equal("nvme-sector-probe-completion-error")
expect(nvme_sector_probe_reason(nvme_sector_probe_result(8u64, 512u64, 0u32, false, true, true, true))).to_equal("nvme-sector-probe-read-missing")
expect(nvme_sector_probe_reason(nvme_sector_probe_result(8u64, 512u64, 0u32, true, false, true, true))).to_equal("nvme-sector-probe-write-missing")
expect(nvme_sector_probe_reason(nvme_sector_probe_result(8u64, 512u64, 0u32, true, true, false, true))).to_equal("nvme-sector-probe-restore-missing")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_sector_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe sector probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
