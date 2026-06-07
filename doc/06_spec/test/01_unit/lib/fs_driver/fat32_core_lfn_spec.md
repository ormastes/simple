# Fat32 Core Lfn Specification

> 1. var driver =  mounted lfn driver

<!-- sdn-diagram:id=fat32_core_lfn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fat32_core_lfn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fat32_core_lfn_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fat32_core_lfn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fat32 Core Lfn Specification

## Scenarios

### shared Fat32Core long filename directory reads

#### lists a single-slot LFN instead of the backing 8.3 alias

1. var driver =  mounted lfn driver
   - Expected: entries.is_ok() is true
   - Expected: listed.len() equals `1`
   - Expected: listed[0].name equals `browser_demo`
   - Expected: listed[0].inode.id equals `5u64`
   - Expected: listed[0].size equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = _mounted_lfn_driver()
val entries = driver.read_dir_entries(2u32)
expect(entries.is_ok()).to_equal(true)
val listed = entries.unwrap()
expect(listed.len()).to_equal(1)
expect(listed[0].name).to_equal("browser_demo")
expect(listed[0].inode.id).to_equal(5u64)
expect(listed[0].size).to_equal(12345)
```

</details>

#### resolves the LFN case-insensitively through shared Fat32Core

1. var driver =  mounted lfn driver
   - Expected: lower.is_ok() is true
   - Expected: upper.is_ok() is true
   - Expected: lower.unwrap().name equals `browser_demo`
   - Expected: upper.unwrap().inode.id equals `5u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = _mounted_lfn_driver()
val lower = driver.resolve_path("/browser_demo")
val upper = driver.resolve_path("/BROWSER_DEMO")
expect(lower.is_ok()).to_equal(true)
expect(upper.is_ok()).to_equal(true)
expect(lower.unwrap().name).to_equal("browser_demo")
expect(upper.unwrap().inode.id).to_equal(5u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared Fat32Core long filename directory reads

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
