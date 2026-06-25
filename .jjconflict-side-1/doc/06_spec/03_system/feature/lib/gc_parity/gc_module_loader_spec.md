# GC-Mode Module Resolution

> Verifies that the module loader resolves modules from the correct variant directories. Tests that common/ modules are accessible and that the fallback chain works after migration.

<!-- sdn-diagram:id=gc_module_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_module_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_module_loader_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_module_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GC-Mode Module Resolution

Verifies that the module loader resolves modules from the correct variant directories. Tests that common/ modules are accessible and that the fallback chain works after migration.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/lib/gc_parity/gc_module_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the module loader resolves modules from the correct
variant directories. Tests that common/ modules are accessible
and that the fallback chain works after migration.

## Scenarios

### Module Resolution Fallback

#### when importing array utilities from common

#### accesses array utilities after migration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [3, 1, 2]
expect(items[0]).to_equal(3)
expect(items.len()).to_equal(3)
```

</details>

#### when verifying omitted sync GC family

#### does not expose an unimplemented gc_sync_mut family

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has_gc_sync_mut_source_dir()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
