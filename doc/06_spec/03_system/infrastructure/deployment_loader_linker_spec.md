# Deployment Loader Linker Specification

> <details>

<!-- sdn-diagram:id=deployment_loader_linker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=deployment_loader_linker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

deployment_loader_linker_spec -> compiler
deployment_loader_linker_spec -> app
deployment_loader_linker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=deployment_loader_linker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deployment Loader Linker Specification

## Scenarios

### Loader/Linker deployment coverage

#### exercises loader and linker wrapper smoke paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = NativeLinkConfig.default()
val smf_inputs = ["module.smf", "archive.lsm", "native.o", "notes.txt"]

expect(cfg.pie).to_equal(true)
expect(cfg.verbose).to_equal(false)
expect(link_to_native([], "out.bin", cfg).is_err()).to_equal(true)
expect(link_to_native(["module.smf", "native.o"], "out.bin", cfg).is_err()).to_equal(true)
expect(smf_inputs.len()).to_equal(4)
```

</details>

#### scans libraries through the shared provider and exposes module data

1.   = shell
2. delete if exists
3. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data_with_object("pkg/core", [1, 2, 3, 4], [127, 69, 76, 70, 1]).is_ok() is true
   - Expected: builder.add_module_data("pkg/fallback", [9, 8, 7]).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
   - Expected: scan_result.is_ok() is true
   - Expected: libraries.len() equals `1`
   - Expected: libraries[0].name equals `deployment_fixture`
   - Expected: libraries[0].modules contains `pkg/core`
   - Expected: libraries[0].modules contains `pkg/fallback`
   - Expected: provider.add_library(lib_path).is_ok() is true
   - Expected: provider.get_module_bytes("pkg/core").unwrap() equals `[1, 2, 3, 4]`
   - Expected: provider.get_object("pkg/core").unwrap() equals `[127, 69, 76, 70, 1]`
   - Expected: provider.get_exported_code("pkg/fallback").unwrap()[0].bytes equals `[9, 8, 7]`
4. delete if exists
5.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_dir = "/tmp/unit_deployment_loader_linker_scan"
val lib_path = "{temp_dir}/deployment_fixture.lsm"
_ = shell("mkdir -p '{temp_dir}'")
delete_if_exists(lib_path)

var builder = LibSmfBuilder.new()
expect(builder.add_module_data_with_object("pkg/core", [1, 2, 3, 4], [127, 69, 76, 70, 1]).is_ok()).to_equal(true)
expect(builder.add_module_data("pkg/fallback", [9, 8, 7]).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)

val scan_result = scan_libraries([temp_dir], false)
expect(scan_result.is_ok()).to_equal(true)
val libraries = scan_result.unwrap()
expect(libraries.len()).to_equal(1)
expect(libraries[0].name).to_equal("deployment_fixture")
expect(libraries[0].modules.contains("pkg/core")).to_equal(true)
expect(libraries[0].modules.contains("pkg/fallback")).to_equal(true)

var provider = ObjectProvider.new(ObjectProviderConfig(
    search_paths: [temp_dir],
    libraries: [lib_path],
    enable_cache: true,
    verbose: false,
    prefer_backend: ""
))
expect(provider.add_library(lib_path).is_ok()).to_equal(true)
expect(provider.get_module_bytes("pkg/core").unwrap()).to_equal([1, 2, 3, 4])
expect(provider.get_object("pkg/core").unwrap()).to_equal([127, 69, 76, 70, 1])
expect(provider.get_exported_code("pkg/fallback").unwrap()[0].bytes).to_equal([9, 8, 7])

delete_if_exists(lib_path)
_ = shell("rmdir '{temp_dir}' 2>/dev/null || true")
```

</details>

#### extracts object files from resolved modules and code units

1.   = shell
2. delete if exists
   - Expected: extract_result.is_ok() is true
   - Expected: extract_result.unwrap().len() equals `1`
   - Expected: extract_result.unwrap()[0] equals `object_path`
   - Expected: rt_file_exists(object_path) is true
3. delete if exists
   - Expected: fallback_extract.is_ok() is true
   - Expected: fallback_extract.unwrap()[0] equals `fallback_path`
   - Expected: rt_file_exists(fallback_path) is true
4. delete if exists
5. delete if exists
6.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_dir = "/tmp/unit_deployment_loader_linker_extract"
_ = shell("mkdir -p '{temp_dir}'")

val object_path = "{temp_dir}/simple_lib_pkg_core.o"
delete_if_exists(object_path)

val resolved = [
    ResolvedModule(
        module_name: "pkg/core",
        library_path: "/tmp/deployment_fixture.lsm",
        smf_data: [1, 2, 3, 4],
        has_object: true,
        obj_data: [127, 69, 76, 70, 1],
        has_code_units: false,
        code_units: []
    )
]

val extract_result = extract_objects_from_resolved(resolved, temp_dir, false)
expect(extract_result.is_ok()).to_equal(true)
expect(extract_result.unwrap().len()).to_equal(1)
expect(extract_result.unwrap()[0]).to_equal(object_path)
expect(rt_file_exists(object_path)).to_equal(true)

val fallback_code = if host_arch() == "aarch64":
    [0xC0, 0x03, 0x5F, 0xD6]
else:
    [0xC3]
val fallback_unit = make_object_code_unit("pkg/fallback", fallback_code)
val fallback_resolved = [
    ResolvedModule(
        module_name: "pkg/fallback",
        library_path: "/tmp/deployment_fixture.lsm",
        smf_data: [5, 6, 7, 8],
        has_object: false,
        obj_data: [],
        has_code_units: true,
        code_units: [fallback_unit]
    )
]
val fallback_path = "{temp_dir}/simple_lib_pkg_fallback.o"
delete_if_exists(fallback_path)

val fallback_extract = extract_objects_from_resolved(fallback_resolved, temp_dir, false)
expect(fallback_extract.is_ok()).to_equal(true)
expect(fallback_extract.unwrap()[0]).to_equal(fallback_path)
expect(rt_file_exists(fallback_path)).to_equal(true)

delete_if_exists(object_path)
delete_if_exists(fallback_path)
_ = shell("rmdir '{temp_dir}' 2>/dev/null || true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/deployment_loader_linker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Loader/Linker deployment coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
