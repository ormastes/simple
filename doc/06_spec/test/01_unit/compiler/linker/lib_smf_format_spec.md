# Lib Smf Format Specification

> <details>

<!-- sdn-diagram:id=lib_smf_format_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lib_smf_format_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lib_smf_format_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lib_smf_format_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lib Smf Format Specification

## Scenarios

### Lib Smf Format

#### creates and round-trips an index entry without an object file

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ModuleIndexEntry.new("test/module", 128, 1024, 12345)
expect(entry.get_name()).to_equal("test/module")
expect(entry.has_object()).to_equal(false)
expect(entry.to_bytes().len()).to_equal(128)

val restored = ModuleIndexEntry.from_bytes(entry.to_bytes(), 0).unwrap()
expect(restored.get_name()).to_equal("test/module")
expect(restored.offset as i64).to_equal(128)
expect(restored.size as i64).to_equal(1024)
```

</details>

#### creates and round-trips an index entry with an object file

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ModuleIndexEntry.new_with_object("std/io/mod", 1000, 2000, 111111, 3000, 500, 222222)
expect(entry.has_object()).to_equal(true)

val restored = ModuleIndexEntry.from_bytes(entry.to_bytes(), 0).unwrap()
expect(restored.get_name()).to_equal("std/io/mod")
expect(restored.obj_offset as i64).to_equal(3000)
expect(restored.obj_size as i64).to_equal(500)
expect(restored.obj_hash as i64).to_equal(222222)
```

</details>

#### serializes and validates the library header

1. var header = LibSmfHeader new default
   - Expected: bytes.len() equals `128`
   - Expected: restored.is_valid() is true
   - Expected: restored.module_count as i64 equals `42`
   - Expected: restored.library_hash as i64 equals `999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var header = LibSmfHeader.new_default()
header.module_count = 42
header.library_hash = 999999

val bytes = header.to_bytes()
expect(bytes.len()).to_equal(128)

val restored = LibSmfHeader.from_bytes(bytes).unwrap()
expect(restored.is_valid()).to_equal(true)
expect(restored.module_count as i64).to_equal(42)
expect(restored.library_hash as i64).to_equal(999999)
```

</details>

#### produces stable hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fnv1a_hash([1, 2, 3, 4, 5])).to_equal(fnv1a_hash([1, 2, 3, 4, 5]))
expect(fnv1a_hash([1, 2, 3])).to_equal(fnv1a_hash([1, 2, 3]))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/lib_smf_format_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lib Smf Format

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
