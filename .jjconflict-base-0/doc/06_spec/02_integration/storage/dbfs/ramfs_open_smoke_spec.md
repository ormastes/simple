# Ramfs Open Smoke Specification

> 1. var d = RamFsDriver new

<!-- sdn-diagram:id=ramfs_open_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ramfs_open_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ramfs_open_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ramfs_open_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ramfs Open Smoke Specification

## Scenarios

### RamFS direct open smoke

#### open creates a file and returns valid handle

1. var d = RamFsDriver new
2. d mount
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = RamFsDriver.new()
d.mount(MountOptions.default()).unwrap()
val fh = d.open(Path(raw: "/x"), OpenFlags.create_write()).unwrap()
val ok = fh.id > 0
expect(ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/ramfs_open_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RamFS direct open smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
