# Nvfs Name Persistence Specification

> <details>

<!-- sdn-diagram:id=nvfs_name_persistence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_name_persistence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_name_persistence_spec -> std
nvfs_name_persistence_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_name_persistence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Name Persistence Specification

## Scenarios

### NvfsPosixDriver name table persistence

#### file created on first mount survives remount

- var dev =  make persist device
   - Expected: res.file_found is true
   - Expected: res.read_ok is true
   - Expected: res.read_n equals `3`
   - Expected: res.first_byte equals `0xABu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_persist_device()
val res = _do_write_remount_read(dev)
expect(res.file_found).to_equal(true)
expect(res.read_ok).to_equal(true)
expect(res.read_n).to_equal(3)
expect(res.first_byte).to_equal(0xABu8)
```

</details>

#### multiple files persist across remount

- var dev =  make persist device
   - Expected: found equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_persist_device()
val found = _do_multi_file_remount(dev)
expect(found).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/nvfs/nvfs_name_persistence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NvfsPosixDriver name table persistence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
