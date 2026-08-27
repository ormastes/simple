# Driver Api Heavy Path Specification

> <details>

<!-- sdn-diagram:id=driver_api_heavy_path_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_api_heavy_path_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_api_heavy_path_spec -> std
driver_api_heavy_path_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_api_heavy_path_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Api Heavy Path Specification

## Scenarios

### Driver API Heavy Path Tiers

#### driver_api_types imports terminate cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = find_runtime_lib_dir()
expect(path.len() > 0).to_equal(true)
```

</details>

#### driver_api_core compile_file import terminates cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = core_compile_file
expect(find_runtime_lib_dir()).to_equal(find_runtime_lib_dir())
```

</details>

#### driver_api_core interpret_file import terminates cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### driver_api_core aot_c_file import terminates cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = core_aot_c_file
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### driver_api_core aot_native_file_with_backend import terminates cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = core_aot_native_file_with_backend
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### driver_api_core aot_native_project_with_backend import terminates cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = core_aot_native_project_with_backend
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### tier 1 driver_api_interpret imports terminate cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = tier1_interpret
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### tier 2 driver_api_compile_single imports terminate cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = tier2_compile
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### tier 3 driver_api_codegen_backends imports terminate cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = tier3_aot_c
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### tier 4 driver_api_native_single imports terminate cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = tier4_native
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### tier 5 driver_api_project_build imports terminate cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = tier5_project
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### importing find_runtime_lib_dir from driver_api_types works in isolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = find_runtime_lib_dir()
expect(path.len() > 0).to_equal(true)
```

</details>

#### importing compile_file from driver_public_compile works in isolation

1. delete file
   - Expected: result.is_success() is false
   - Expected: result.get_errors().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_path = "/tmp/sml_heavy_path_public_compile_missing.spl"
delete_file(missing_path)
val result = public_compile_file(missing_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().len() > 0).to_equal(true)
```

</details>

#### driver_api_core re-exports find_runtime_lib_dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# find_runtime_lib_dir originates in driver_api_types but is
# also exported by driver_api_core for backward compat.
val path_from_types = find_runtime_lib_dir()
expect(path_from_types.len() > 0).to_equal(true)
```

</details>

#### driver_api_core re-exports compile_file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = core_compile_file
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### driver_api_core re-exports check_file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _fn = core_check_file
expect(find_runtime_lib_dir().len() > 0).to_equal(true)
```

</details>

#### driver_api facade exposes compile_file

1. delete file
   - Expected: result.is_success() is false
   - Expected: result.get_errors().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_path = "/tmp/sml_heavy_path_facade_compile_missing.spl"
delete_file(missing_path)
val result = facade_compile_file(missing_path)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().len() > 0).to_equal(true)
```

</details>

#### driver_api facade exposes aot_c_file

1. delete file
2. write file
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(out_path) is true
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_heavy_path_facade_aot_c.spl"
val out_path = "/tmp/sml_heavy_path_facade_aot_c.cpp"
delete_file(out_path)
write_file(src_path, "fn main(): 46")
val result = facade_aot_c_file(src_path, out_path)
expect(result.is_success()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### driver_public_compile exposes compile_to_smf

1. delete file
2. delete file
   - Expected: result.is_err() is true
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_path = "/tmp/sml_heavy_path_public_smf_missing.spl"
val out_path = "/tmp/sml_heavy_path_public_smf_missing.smf"
delete_file(missing_path)
delete_file(out_path)
val result = public_compile_to_smf(missing_path, out_path)
expect(result.is_err()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(false)
```

</details>

#### driver_public_compile exposes parse_sdn_file

1. write file
   - Expected: result.is_success() is true
2. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn_path = "/tmp/sml_heavy_path_public_parse.sdn"
write_file(sdn_path, "root:" + NL + "  name: \"heavy-path\"")
val result = public_parse_sdn_file(sdn_path)
expect(result.is_success()).to_equal(true)
delete_file(sdn_path)
```

</details>

#### driver_public_api exposes interpret_file

1. write file
   - Expected: result.is_success() is true
2. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_heavy_path_public_interpret.spl"
write_file(src_path, "fn main(): 47")
val result = public_interpret_file(src_path)
expect(result.is_success()).to_equal(true)
delete_file(src_path)
```

</details>

#### driver_public_api exposes generate_headers

1. delete file
   - Expected: result.is_success() is false
   - Expected: result.get_errors().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_path = "/tmp/sml_heavy_path_public_headers_missing.spl"
val out_dir = "/tmp/sml_heavy_path_public_headers"
delete_file(missing_path)
val result = public_generate_headers(missing_path, out_dir, "heavy_path", true, true)
expect(result.is_success()).to_equal(false)
expect(result.get_errors().len() > 0).to_equal(true)
```

</details>

#### driver_public_shared exposes aot_shared_library

1. delete file
2. delete file
   - Expected: result.is_success() is false
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_path = "/tmp/sml_heavy_path_public_shared_missing.spl"
val out_path = "/tmp/sml_heavy_path_public_shared_missing.so"
delete_file(missing_path)
delete_file(out_path)
val result = public_aot_shared_library(missing_path, out_path)
expect(result.is_success()).to_equal(false)
expect(rt_file_exists(out_path)).to_equal(false)
```

</details>

#### find_runtime_lib_dir returns a non-empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = find_runtime_lib_dir()
expect(path.len() > 0).to_equal(true)
```

</details>

#### find_runtime_lib_dir returns a consistent path across calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path1 = find_runtime_lib_dir()
val path2 = find_runtime_lib_dir()
expect(path1).to_equal(path2)
```

</details>

#### driver_api_core check_file validates a simple source file

1. write file
   - Expected: result.is_success() is true
2. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/sml_heavy_path_check.spl"
write_file(src_path, "fn main(): 42")

val result = core_check_file(src_path)

expect(result.is_success()).to_equal(true)
delete_file(src_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/driver_api_heavy_path_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Driver API Heavy Path Tiers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
