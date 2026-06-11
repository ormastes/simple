# Lib Smf Reader Specification

> 1. reader close

<!-- sdn-diagram:id=lib_smf_reader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lib_smf_reader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lib_smf_reader_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lib_smf_reader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lib Smf Reader Specification

## Scenarios

### Lib Smf Reader

#### opens a valid library and lists indexed modules

1. reader close
2. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_path = "/tmp/unit_lib_smf_reader_open.lsm"
val reader = build_test_library(lib_path)

expect(reader.module_count()).to_equal(2)
expect(reader.list_modules().contains("alpha/mod")).to_equal(true)
expect(reader.list_modules().contains("beta/mod")).to_equal(true)
expect(reader.has_module("alpha/mod")).to_equal(true)
expect(reader.has_module("gamma/mod")).to_equal(false)

reader.close()
delete_if_exists(lib_path)
```

</details>

#### reads module and object bytes exactly

1. reader close
2. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_path = "/tmp/unit_lib_smf_reader_bytes.lsm"
val reader = build_test_library(lib_path)

expect(reader.get_module("alpha/mod").unwrap()).to_equal([10, 20, 30, 40])
expect(reader.get_module("beta/mod").unwrap()).to_equal([50, 60, 70])
expect(reader.get_object("beta/mod").unwrap()).to_equal([127, 69, 76, 70, 9, 8])
expect(reader.has_object("alpha/mod")).to_equal(false)
expect(reader.has_object("beta/mod")).to_equal(true)

reader.close()
delete_if_exists(lib_path)
```

</details>

#### reports missing files, invalid archives, and missing modules

1. delete if exists
   - Expected: rt_file_write_bytes(invalid_path, [1, 2, 3, 4, 5]) is true
   - Expected: LibSmfReader.open(invalid_path).is_err() is true
   - Expected: reader.get_module("not/present").is_err() is true
   - Expected: reader.get_object("alpha/mod").is_err() is true
2. reader close
3. delete if exists
4. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LibSmfReader.open("/tmp/reader_missing_archive.lsm").is_err()).to_equal(true)

val invalid_path = "/tmp/unit_lib_smf_reader_invalid.lsm"
delete_if_exists(invalid_path)
expect(rt_file_write_bytes(invalid_path, [1, 2, 3, 4, 5])).to_equal(true)
expect(LibSmfReader.open(invalid_path).is_err()).to_equal(true)

val lib_path = "/tmp/unit_lib_smf_reader_errors.lsm"
val reader = build_test_library(lib_path)
expect(reader.get_module("not/present").is_err()).to_equal(true)
expect(reader.get_object("alpha/mod").is_err()).to_equal(true)

reader.close()
delete_if_exists(invalid_path)
delete_if_exists(lib_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/lib_smf_reader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lib Smf Reader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
