# Lockfile Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=lockfile_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lockfile_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lockfile_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lockfile_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lockfile Numeric Guard Specification

## Scenarios

### package lockfile numeric guard

#### defaults malformed lockfile version parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nogc_sync = rt_file_read_text("src/lib/nogc_sync_mut/package/lockfile.spl") ?? ""
val nogc_async = rt_file_read_text("src/lib/nogc_async_mut/package/lockfile.spl") ?? ""
val gc_async = rt_file_read_text("src/lib/gc_async_mut/package/lockfile.spl") ?? ""

expect(nogc_sync).to_contain("version = v.to_int() ?? 1")
expect(nogc_async).to_contain("version = v.to_int() ?? 1")
expect(gc_async).to_contain("version = v.to_int() ?? 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/package/lockfile_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- package lockfile numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
