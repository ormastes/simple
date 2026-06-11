# Link With Libraries Integration Specification

> 1.   = shell

<!-- sdn-diagram:id=link_with_libraries_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=link_with_libraries_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

link_with_libraries_integration_spec -> compiler
link_with_libraries_integration_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=link_with_libraries_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Link With Libraries Integration Specification

## Scenarios

### Link With Libraries Integration

#### discovers libraries created on disk

1.   = shell
2. delete if exists
3. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data("test/module", [1, 2, 3, 4]).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
   - Expected: result.is_ok() is true
   - Expected: libraries.len() equals `1`
   - Expected: libraries[0].name equals `sample`
   - Expected: libraries[0].modules contains `test/module`
4. delete if exists
5.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_dir = "/tmp/unit_link_with_libraries_scan"
val lib_path = "{lib_dir}/sample.lsm"
_ = shell("mkdir -p '{lib_dir}'")
delete_if_exists(lib_path)

var builder = LibSmfBuilder.new()
expect(builder.add_module_data("test/module", [1, 2, 3, 4]).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)

val result = scan_libraries([lib_dir], false)
expect(result.is_ok()).to_equal(true)
val libraries = result.unwrap()
expect(libraries.len()).to_equal(1)
expect(libraries[0].name).to_equal("sample")
expect(libraries[0].modules.contains("test/module")).to_equal(true)

delete_if_exists(lib_path)
_ = shell("rmdir '{lib_dir}' 2>/dev/null || true")
```

</details>

#### writes binary data and supports empty payloads

1. delete if exists
2. delete if exists
   - Expected: write_bytes_to_file(bytes_path, [72, 101, 108, 108, 111]) is true
   - Expected: write_bytes_to_file(empty_path, []) is true
   - Expected: rt_file_exists(bytes_path) is true
   - Expected: rt_file_exists(empty_path) is true
3. delete if exists
4. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes_path = "/tmp/unit_link_with_libraries_bytes.bin"
val empty_path = "/tmp/unit_link_with_libraries_empty.bin"
delete_if_exists(bytes_path)
delete_if_exists(empty_path)

expect(write_bytes_to_file(bytes_path, [72, 101, 108, 108, 111])).to_equal(true)
expect(write_bytes_to_file(empty_path, [])).to_equal(true)
expect(rt_file_exists(bytes_path)).to_equal(true)
expect(rt_file_exists(empty_path)).to_equal(true)

delete_if_exists(bytes_path)
delete_if_exists(empty_path)
```

</details>

#### extracts resolved object payloads to temporary files

1. delete if exists
2.   = shell
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().len() equals `1`
   - Expected: result.unwrap()[0] equals `obj_path`
   - Expected: rt_file_exists(obj_path) is true
3. delete if exists
4.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_dir = "/tmp/unit_link_with_libraries_extract"
val obj_path = "{temp_dir}/simple_lib_pkg_core.o"
delete_if_exists(obj_path)
_ = shell("mkdir -p '{temp_dir}'")

val resolved = [
    ResolvedModule(
        module_name: "pkg/core",
        library_path: "/tmp/sample.lsm",
        smf_data: [10, 11, 12],
        has_object: true,
        obj_data: [127, 69, 76, 70, 1, 2, 3],
        has_code_units: false,
        code_units: []
    )
]

val result = extract_objects_from_resolved(resolved, temp_dir, false)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().len()).to_equal(1)
expect(result.unwrap()[0]).to_equal(obj_path)
expect(rt_file_exists(obj_path)).to_equal(true)

delete_if_exists(obj_path)
_ = shell("rmdir '{temp_dir}' 2>/dev/null || true")
```

</details>

#### rejects resolved modules that have no object payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = [
    ResolvedModule(
        module_name: "pkg/missing",
        library_path: "/tmp/sample.lsm",
        smf_data: [1],
        has_object: false,
        obj_data: [],
        has_code_units: false,
        code_units: []
    )
]

val result = extract_objects_from_resolved(resolved, "/tmp/unit_link_with_libraries_missing", false)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/link_with_libraries_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Link With Libraries Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
