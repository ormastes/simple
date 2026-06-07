# Dependency Boundary Specification

> <details>

<!-- sdn-diagram:id=dependency_boundary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dependency_boundary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dependency_boundary_spec -> std
dependency_boundary_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dependency_boundary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dependency Boundary Specification

## Scenarios

### Library dependency boundary

#### has no unapproved direct os imports from src/lib

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_lib_os_import_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### has no direct POSIX or Linux namespace imports from src/lib

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_lib_posix_linux_namespace_import_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### does not let no-GC sync libs import GC async libs directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_nogc_sync_imports_gc_async_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### does not let no-GC async libs import GC async libs directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_nogc_async_imports_gc_async_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### does not let GC async libs import no-GC sync libs directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_gc_async_imports_nogc_sync_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### does not let noalloc libs import allocating runtime families directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_noalloc_imports_allocating_family_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### does not let noalloc libs import app surfaces directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_noalloc_app_import_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### does not let noalloc libs opt into allocation annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_noalloc_alloc_annotation_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### does not let noalloc libs call host allocation APIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_noalloc_host_allocation_api_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### keeps the noalloc reachable import closure in noalloc or common

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = verify_noalloc_reachable_imports()
expect(unexpected.len()).to_equal(0)
```

</details>

#### has no direct examples imports from src/lib

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_lib_examples_import_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### has no direct examples imports from src/os

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_os_examples_import_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### has no direct examples imports from src/app

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_app_examples_import_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### has no direct examples imports from production system specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_system_spec_examples_import_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### has no direct examples imports from library tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_lib_test_examples_import_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### has no direct examples imports from non-generated tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_test_examples_import_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### does not route production code through common pure runtime shell helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _non_empty_scan_lines(_common_pure_runtime_import_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

#### keeps host platform markers inside approved backend or contract paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unexpected = _unapproved_host_platform_marker_lines(_host_platform_marker_scan())
expect(unexpected.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/dependency_boundary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Library dependency boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
