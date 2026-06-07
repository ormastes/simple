# Lib Smf Writer Specification

> 1. var builder = LibSmfBuilder new

<!-- sdn-diagram:id=lib_smf_writer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lib_smf_writer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lib_smf_writer_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lib_smf_writer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lib Smf Writer Specification

## Scenarios

### Lib Smf Writer

#### tracks module count and names for in-memory modules

1. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data("alpha/mod", [1, 2, 3, 4]).is_ok() is true
   - Expected: builder.add_module_data_with_object("beta/mod", [5, 6], [7, 8, 9]).is_ok() is true
   - Expected: builder.module_count() equals `2`
   - Expected: builder.count_objects() equals `1`
   - Expected: builder.module_names() contains `alpha/mod`
   - Expected: builder.module_names() contains `beta/mod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = LibSmfBuilder.new()

expect(builder.add_module_data("alpha/mod", [1, 2, 3, 4]).is_ok()).to_equal(true)
expect(builder.add_module_data_with_object("beta/mod", [5, 6], [7, 8, 9]).is_ok()).to_equal(true)

expect(builder.module_count()).to_equal(2)
expect(builder.count_objects()).to_equal(1)
expect(builder.module_names().contains("alpha/mod")).to_equal(true)
expect(builder.module_names().contains("beta/mod")).to_equal(true)
```

</details>

#### writes a library that round-trips module and object bytes

1. delete if exists
2. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data_with_object("std/io/mod", smf_data, obj_data).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
   - Expected: rt_file_exists(lib_path) is true
   - Expected: restored_smf equals `smf_data`
   - Expected: restored_obj equals `obj_data`
   - Expected: reader.module_count() equals `1`
   - Expected: reader.has_object("std/io/mod") is true
3. reader close
4. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_path = "/tmp/unit_lib_smf_writer_roundtrip.lsm"
delete_if_exists(lib_path)

var builder = LibSmfBuilder.new()
val smf_data = [83, 77, 70, 0, 1, 1, 0, 0, 10, 11, 12]
val obj_data = [127, 69, 76, 70, 1, 2, 3, 4]
expect(builder.add_module_data_with_object("std/io/mod", smf_data, obj_data).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)
expect(rt_file_exists(lib_path)).to_equal(true)

val reader = LibSmfReader.open(lib_path).unwrap()
val restored_smf = reader.get_module("std/io/mod").unwrap()
val restored_obj = reader.get_object("std/io/mod").unwrap()

expect(restored_smf).to_equal(smf_data)
expect(restored_obj).to_equal(obj_data)
expect(reader.module_count()).to_equal(1)
expect(reader.has_object("std/io/mod")).to_equal(true)

reader.close()
delete_if_exists(lib_path)
```

</details>

#### packages an SMF with a driver manifest section without changing DRVS bytes

1. delete if exists
2. var opts = SmfBuildOptions create
3. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data("drivers/ahci", smf_data).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
   - Expected: restored_smf equals `smf_data`
   - Expected: restored_smf contains `0x53`
   - Expected: restored_smf contains `0x56`
   - Expected: restored_smf contains `0x52`
   - Expected: restored_smf contains `0x44`
4. reader close
5. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_path = "/tmp/unit_lib_smf_writer_driver_manifest.lsm"
delete_if_exists(lib_path)

var opts = SmfBuildOptions.create(Target.x86_64_unknown_linux_gnu())
opts.driver_manifest_bytes = [
    0x53, 0x56, 0x52, 0x44,
    0, 3, 1, 0,
    0x86, 0x80, 0, 0,
    1, 0, 0, 0,
    0x22, 0x29, 0, 0
]
val smf_data = generate_smf_with_options([0xC3], opts)

var builder = LibSmfBuilder.new()
expect(builder.add_module_data("drivers/ahci", smf_data).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)

val reader = LibSmfReader.open(lib_path).unwrap()
val restored_smf = reader.get_module("drivers/ahci").unwrap()

expect(restored_smf).to_equal(smf_data)
expect(restored_smf.contains(0x53)).to_equal(true)
expect(restored_smf.contains(0x56)).to_equal(true)
expect(restored_smf.contains(0x52)).to_equal(true)
expect(restored_smf.contains(0x44)).to_equal(true)

reader.close()
delete_if_exists(lib_path)
```

</details>

#### adds module bytes from files and rejects missing inputs

1. delete if exists
2. delete if exists
   - Expected: rt_file_write_bytes(smf_path, [9, 8, 7, 6]) is true
   - Expected: rt_file_write_bytes(obj_path, [1, 3, 3, 7]) is true
3. var builder = LibSmfBuilder new
   - Expected: builder.add_module("file/only", smf_path).is_ok() is true
   - Expected: builder.add_module_with_object("file/with_obj", smf_path, obj_path).is_ok() is true
   - Expected: builder.add_module("missing/mod", "/tmp/not_real_module.smf").is_err() is true
   - Expected: builder.add_module_with_object("missing/obj", smf_path, "/tmp/not_real_module.o").is_err() is true
4. delete if exists
5. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf_path = "/tmp/unit_lib_smf_writer_file_input.smf"
val obj_path = "/tmp/unit_lib_smf_writer_file_input.o"
delete_if_exists(smf_path)
delete_if_exists(obj_path)

expect(rt_file_write_bytes(smf_path, [9, 8, 7, 6])).to_equal(true)
expect(rt_file_write_bytes(obj_path, [1, 3, 3, 7])).to_equal(true)

var builder = LibSmfBuilder.new()
expect(builder.add_module("file/only", smf_path).is_ok()).to_equal(true)
expect(builder.add_module_with_object("file/with_obj", smf_path, obj_path).is_ok()).to_equal(true)
expect(builder.add_module("missing/mod", "/tmp/not_real_module.smf").is_err()).to_equal(true)
expect(builder.add_module_with_object("missing/obj", smf_path, "/tmp/not_real_module.o").is_err()).to_equal(true)

delete_if_exists(smf_path)
delete_if_exists(obj_path)
```

</details>

#### rejects writing an empty library

1. var builder = LibSmfBuilder new
   - Expected: builder.write("/tmp/unit_lib_smf_writer_empty.lsm").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = LibSmfBuilder.new()
expect(builder.write("/tmp/unit_lib_smf_writer_empty.lsm").is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/lib_smf_writer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lib Smf Writer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
