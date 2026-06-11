# Object Provider Specification

> 1.   = shell

<!-- sdn-diagram:id=object_provider_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=object_provider_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

object_provider_spec -> compiler
object_provider_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=object_provider_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Object Provider Specification

## Scenarios

### Object Provider

#### loads library modules and exposes module bytes, object bytes, and code units

1.   = shell
2. delete if exists
3. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data_with_object("pkg/core", [1, 2, 3, 4], [127, 69, 76, 70, 1]).is_ok() is true
   - Expected: builder.add_module_data("pkg/fallback", [9, 8, 7]).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
   - Expected: provider.add_library(lib_path).is_ok() is true
   - Expected: provider.has_module("pkg/core") is true
   - Expected: provider.has_module("pkg/fallback") is true
   - Expected: provider.list_modules() contains `pkg/core`
   - Expected: provider.list_modules() contains `pkg/fallback`
   - Expected: provider.get_module_bytes("pkg/core").unwrap() equals `[1, 2, 3, 4]`
   - Expected: provider.get_object("pkg/core").unwrap() equals `[127, 69, 76, 70, 1]`
   - Expected: code_units.len() equals `1`
   - Expected: code_units[0].name equals `pkg/fallback`
   - Expected: code_units[0].bytes equals `[9, 8, 7]`
   - Expected: code_units[0].size equals `3`
4. delete if exists
5.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_dir = "/tmp/unit_object_provider_spec"
val lib_path = "{temp_dir}/provider_fixture.lsm"
_ = shell("mkdir -p '{temp_dir}'")
delete_if_exists(lib_path)

var builder = LibSmfBuilder.new()
expect(builder.add_module_data_with_object("pkg/core", [1, 2, 3, 4], [127, 69, 76, 70, 1]).is_ok()).to_equal(true)
expect(builder.add_module_data("pkg/fallback", [9, 8, 7]).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)

val provider = ObjectProvider.new(ObjectProviderConfig(
    search_paths: [temp_dir],
    libraries: [],
    enable_cache: true,
    verbose: false,
    prefer_backend: ""
))

expect(provider.add_library(lib_path).is_ok()).to_equal(true)
expect(provider.has_module("pkg/core")).to_equal(true)
expect(provider.has_module("pkg/fallback")).to_equal(true)
expect(provider.list_modules().contains("pkg/core")).to_equal(true)
expect(provider.list_modules().contains("pkg/fallback")).to_equal(true)

expect(provider.get_module_bytes("pkg/core").unwrap()).to_equal([1, 2, 3, 4])
expect(provider.get_object("pkg/core").unwrap()).to_equal([127, 69, 76, 70, 1])

val code_units = provider.get_exported_code("pkg/fallback").unwrap()
expect(code_units.len()).to_equal(1)
expect(code_units[0].name).to_equal("pkg/fallback")
expect(code_units[0].bytes).to_equal([9, 8, 7])
expect(code_units[0].size).to_equal(3)

delete_if_exists(lib_path)
_ = shell("rmdir '{temp_dir}' 2>/dev/null || true")
```

</details>

#### returns errors for missing modules

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = ObjectProvider.new(ObjectProviderConfig(
    search_paths: [],
    libraries: [],
    enable_cache: true,
    verbose: false,
    prefer_backend: ""
))

expect(provider.get_module_bytes("missing/mod").is_err()).to_equal(true)
expect(provider.get_object("missing/mod").is_err()).to_equal(true)
expect(provider.get_exported_code("missing/mod").is_err()).to_equal(true)
```

</details>

#### rejects prefer_backend when the module cannot prove a matching backend

1.   = shell
2. delete if exists
3. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data_with_object("pkg/core", [1, 2, 3, 4], [127, 69, 76, 70, 1]).is_ok() is true
   - Expected: builder.add_module_data("pkg/fallback", [9, 8, 7]).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
   - Expected: provider.add_library(lib_path).is_ok() is true
   - Expected: object_result.is_err() is true
   - Expected: code_result.is_err() is true
4. delete if exists
5.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_dir = "/tmp/unit_object_provider_backend_spec"
val lib_path = "{temp_dir}/provider_backend_fixture.lsm"
_ = shell("mkdir -p '{temp_dir}'")
delete_if_exists(lib_path)

var builder = LibSmfBuilder.new()
expect(builder.add_module_data_with_object("pkg/core", [1, 2, 3, 4], [127, 69, 76, 70, 1]).is_ok()).to_equal(true)
expect(builder.add_module_data("pkg/fallback", [9, 8, 7]).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)

val provider = ObjectProvider.new(ObjectProviderConfig(
    search_paths: [temp_dir],
    libraries: [],
    enable_cache: true,
    verbose: false,
    prefer_backend: "llvm"
))

expect(provider.add_library(lib_path).is_ok()).to_equal(true)
val object_result = provider.get_object("pkg/core")
expect(object_result.is_err()).to_equal(true)
expect(object_result.unwrap_err()).to_contain("prefer_backend=llvm")
expect(object_result.unwrap_err()).to_contain("missing compile options hash")

val code_result = provider.get_exported_code("pkg/fallback")
expect(code_result.is_err()).to_equal(true)
expect(code_result.unwrap_err()).to_contain("prefer_backend=llvm")

delete_if_exists(lib_path)
_ = shell("rmdir '{temp_dir}' 2>/dev/null || true")
```

</details>

#### accepts prefer_backend when the module proves a matching PIC llvm build

1.   = shell
2. delete if exists
3. build smf with code for target
4. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data_with_object("pkg/llvm", smf_data, [127, 69, 76, 70, 1]).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
   - Expected: provider.add_library(lib_path).is_ok() is true
   - Expected: object_result.is_ok() is true
   - Expected: object_result.unwrap() equals `[127, 69, 76, 70, 1]`
   - Expected: code_result.is_ok() is true
   - Expected: code_result.unwrap().len() equals `1`
   - Expected: code_result.unwrap()[0].name equals `pkg/llvm`
5. delete if exists
6.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_dir = "/tmp/unit_object_provider_backend_ok_spec"
val lib_path = "{temp_dir}/provider_backend_ok_fixture.lsm"
_ = shell("mkdir -p '{temp_dir}'")
delete_if_exists(lib_path)

val smf_data = mark_smf_as_pic_for_backend(
    build_smf_with_code_for_target([0xC3], Target.x86_64_unknown_linux_gnu()),
    "llvm-lib"
)

var builder = LibSmfBuilder.new()
expect(builder.add_module_data_with_object("pkg/llvm", smf_data, [127, 69, 76, 70, 1]).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)

val provider = ObjectProvider.new(ObjectProviderConfig(
    search_paths: [temp_dir],
    libraries: [],
    enable_cache: true,
    verbose: false,
    prefer_backend: "llvm"
))

expect(provider.add_library(lib_path).is_ok()).to_equal(true)
val object_result = provider.get_object("pkg/llvm")
expect(object_result.is_ok()).to_equal(true)
expect(object_result.unwrap()).to_equal([127, 69, 76, 70, 1])

val code_result = provider.get_exported_code("pkg/llvm")
expect(code_result.is_ok()).to_equal(true)
expect(code_result.unwrap().len()).to_equal(1)
expect(code_result.unwrap()[0].name).to_equal("pkg/llvm")

delete_if_exists(lib_path)
_ = shell("rmdir '{temp_dir}' 2>/dev/null || true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/object_provider_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Object Provider

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
