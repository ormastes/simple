# Shb Mtime Specification

> <details>

<!-- sdn-diagram:id=shb_mtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shb_mtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shb_mtime_spec -> compiler
shb_mtime_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shb_mtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shb Mtime Specification

## Scenarios

### SHB source mtime header

#### round-trips source mtime through the real writer and reader

- file delete
   - Expected: shb_write_with_source_mtime(iface, path, 333) is true
   - Expected: reader.is_valid() is true
   - Expected: reader.source_hash() equals `111`
   - Expected: reader.interface_hash() equals `222`
   - Expected: reader.source_mtime() equals `333`
- file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_shb_mtime_spec.shb"
file_delete(path)

val iface = shb_module_interface_new(111, 222)

expect(shb_write_with_source_mtime(iface, path, 333)).to_equal(true)

val reader = ShbReader.open(path)
expect(reader.is_valid()).to_equal(true)
expect(reader.source_hash()).to_equal(111)
expect(reader.interface_hash()).to_equal(222)
expect(reader.source_mtime()).to_equal(333)

file_delete(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/cache/shb_mtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHB source mtime header

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
