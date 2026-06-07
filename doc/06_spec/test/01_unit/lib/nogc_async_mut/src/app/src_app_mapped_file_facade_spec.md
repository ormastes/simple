# Src App Mapped File Facade Specification

> <details>

<!-- sdn-diagram:id=src_app_mapped_file_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=src_app_mapped_file_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

src_app_mapped_file_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=src_app_mapped_file_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Src App Mapped File Facade Specification

## Scenarios

### nogc_async_mut src app mapped file facade

#### re-exports mapped file record and bounds checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapped = MappedFile(address: 1, size: 4, path: "/tmp/data")
expect(mapped.is_valid()).to_equal(true)
expect(mapped.file_size()).to_equal(4)
expect(mapped.read_bytes(0, 4).is_ok()).to_equal(true)
expect(mapped.read_string(0, 4).is_ok()).to_equal(true)
expect(mapped.read_bytes(3, 2).is_err()).to_equal(true)
expect(MappedFile.open("/missing").is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/src/app/src_app_mapped_file_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut src app mapped file facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
