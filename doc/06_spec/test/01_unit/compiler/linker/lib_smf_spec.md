# Lib Smf Specification

> 1. var header = LibSmfHeader new default

<!-- sdn-diagram:id=lib_smf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lib_smf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lib_smf_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lib_smf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lib Smf Specification

## Scenarios

### Lib Smf

#### round-trips header and index metadata

1. var header = LibSmfHeader new default
   - Expected: restored_header.is_valid() is true
   - Expected: restored_header.module_count as i64 equals `3`
   - Expected: restored_header.library_hash as i64 equals `123456`
   - Expected: restored_entry.get_name() equals `lib/core`
   - Expected: restored_entry.has_object() is true
   - Expected: restored_entry.obj_offset as i64 equals `192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var header = LibSmfHeader.new_default()
header.module_count = 3
header.library_hash = 123456

val header_bytes = header.to_bytes()
val restored_header = LibSmfHeader.from_bytes(header_bytes).unwrap()
expect(restored_header.is_valid()).to_equal(true)
expect(restored_header.module_count as i64).to_equal(3)
expect(restored_header.library_hash as i64).to_equal(123456)

val entry = ModuleIndexEntry.new_with_object("lib/core", 128, 64, 111, 192, 32, 222)
val restored_entry = ModuleIndexEntry.from_bytes(entry.to_bytes(), 0).unwrap()
expect(restored_entry.get_name()).to_equal("lib/core")
expect(restored_entry.has_object()).to_equal(true)
expect(restored_entry.obj_offset as i64).to_equal(192)
```

</details>

#### round-trips a library through writer and reader

1. delete if exists
2. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data("math/add", [1, 2, 3, 4, 5]).is_ok() is true
   - Expected: builder.add_module_data_with_object("math/mul", [6, 7, 8], [127, 69, 76, 70]).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
   - Expected: reader.module_count() equals `2`
   - Expected: reader.get_module("math/add").unwrap() equals `[1, 2, 3, 4, 5]`
   - Expected: reader.get_object("math/mul").unwrap() equals `[127, 69, 76, 70]`
3. reader close
4. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_path = "/tmp/unit_lib_smf_spec_roundtrip.lsm"
delete_if_exists(lib_path)

var builder = LibSmfBuilder.new()
expect(builder.add_module_data("math/add", [1, 2, 3, 4, 5]).is_ok()).to_equal(true)
expect(builder.add_module_data_with_object("math/mul", [6, 7, 8], [127, 69, 76, 70]).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)

val reader = LibSmfReader.open(lib_path).unwrap()
expect(reader.module_count()).to_equal(2)
expect(reader.get_module("math/add").unwrap()).to_equal([1, 2, 3, 4, 5])
expect(reader.get_object("math/mul").unwrap()).to_equal([127, 69, 76, 70])

reader.close()
delete_if_exists(lib_path)
```

</details>

#### indexes library modules through smf getter

1. delete if exists
2. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data("pkg/foo", [9, 9, 1]).is_ok() is true
   - Expected: builder.add_module_data_with_object("pkg/bar", [9, 9, 2], [127, 69, 76, 70, 0]).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
3. var getter = SmfGetter new
   - Expected: getter.add_library(lib_path).is_ok() is true
   - Expected: getter.has_module("pkg/foo") is true
   - Expected: getter.has_module("pkg/bar") is true
   - Expected: getter.get("pkg/foo").unwrap() equals `[9, 9, 1]`
   - Expected: getter.get_object("pkg/bar").unwrap() equals `[127, 69, 76, 70, 0]`
4. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_path = "/tmp/unit_lib_smf_spec_getter.lsm"
delete_if_exists(lib_path)

var builder = LibSmfBuilder.new()
expect(builder.add_module_data("pkg/foo", [9, 9, 1]).is_ok()).to_equal(true)
expect(builder.add_module_data_with_object("pkg/bar", [9, 9, 2], [127, 69, 76, 70, 0]).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)

var getter = SmfGetter.new()
expect(getter.add_library(lib_path).is_ok()).to_equal(true)
expect(getter.has_module("pkg/foo")).to_equal(true)
expect(getter.has_module("pkg/bar")).to_equal(true)
expect(getter.get("pkg/foo").unwrap()).to_equal([9, 9, 1])
expect(getter.get_object("pkg/bar").unwrap()).to_equal([127, 69, 76, 70, 0])

delete_if_exists(lib_path)
```

</details>

#### produces deterministic hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fnv1a_hash([1, 2, 3])).to_equal(fnv1a_hash([1, 2, 3]))
expect(fnv1a_hash([1, 2, 3])).to_equal(fnv1a_hash([1, 2, 3]))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/lib_smf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lib Smf

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
