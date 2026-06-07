# Linker Wrapper Smf Specification

> <details>

<!-- sdn-diagram:id=linker_wrapper_smf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linker_wrapper_smf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linker_wrapper_smf_spec -> compiler
linker_wrapper_smf_spec -> app
linker_wrapper_smf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linker_wrapper_smf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linker Wrapper Smf Specification

## Scenarios

### Linker Wrapper Smf

#### rejects mixed SMF and object inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = NativeLinkConfig.default()
val result = link_to_native(["a.smf", "b.o"], "out.bin", cfg)
expect(result.is_err()).to_equal(true)
```

</details>

#### errors on empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = NativeLinkConfig.default()
val result = link_to_native([], "out.bin", cfg)
expect(result.is_err()).to_equal(true)
```

</details>

#### extracts object files for resolved modules with object payloads

1.   = shell
2. delete if exists
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
val temp_dir = "/tmp/unit_linker_wrapper_smf_extract"
val obj_path = "{temp_dir}/simple_lib_pkg_core.o"
_ = shell("mkdir -p '{temp_dir}'")
delete_if_exists(obj_path)

val resolved = [
    ResolvedModule(
        module_name: "pkg/core",
        library_path: "/tmp/library_fixture.lsm",
        smf_data: [1, 2, 3],
        has_object: true,
        obj_data: [127, 69, 76, 70, 1],
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

#### assembles code units through the fallback path

1.   = shell
2. delete if exists
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().len() equals `1`
   - Expected: result.unwrap()[0] equals `fallback_path`
   - Expected: rt_file_exists(fallback_path) is true
3. delete if exists
4.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_dir = "/tmp/unit_linker_wrapper_smf_fallback"
val fallback_path = "{temp_dir}/simple_lib_pkg_fallback.o"
_ = shell("mkdir -p '{temp_dir}'")
delete_if_exists(fallback_path)

val fallback_code = if host_arch() == "aarch64":
    [0xC0, 0x03, 0x5F, 0xD6]
else:
    [0xC3]
val fallback_unit = make_object_code_unit("pkg/fallback", fallback_code)
val resolved = [
    ResolvedModule(
        module_name: "pkg/fallback",
        library_path: "/tmp/library_fixture.lsm",
        smf_data: [4, 5, 6],
        has_object: false,
        obj_data: [],
        has_code_units: true,
        code_units: [fallback_unit]
    )
]

val result = extract_objects_from_resolved(resolved, temp_dir, false)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().len()).to_equal(1)
expect(result.unwrap()[0]).to_equal(fallback_path)
expect(rt_file_exists(fallback_path)).to_equal(true)

delete_if_exists(fallback_path)
_ = shell("rmdir '{temp_dir}' 2>/dev/null || true")
```

</details>

#### treats fixed-be as a strict backend selection for invalid SMF input

1.   = shell
2. delete if exists
3. delete if exists
4. delete if exists
5.   = shell
   - Expected: default_result.is_ok() is true
6. fixed cfg extra flags = fixed cfg extra flags push
   - Expected: fixed_result.is_err() is true
7. delete if exists
8. delete if exists
9. delete if exists
10.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_dir = "/tmp/unit_linker_wrapper_fixed_be"
val bad_smf = "{temp_dir}/invalid_input.smf"
val out_default = "{temp_dir}/default.out"
val out_fixed = "{temp_dir}/fixed.out"
_ = shell("mkdir -p '{temp_dir}'")
delete_if_exists(bad_smf)
delete_if_exists(out_default)
delete_if_exists(out_fixed)
_ = shell("printf 'not a real smf' > '{bad_smf}'")

val default_cfg = NativeLinkConfig.default()
val default_result = link_to_native([bad_smf], out_default, default_cfg)
expect(default_result.is_ok()).to_equal(true)

val fixed_cfg = NativeLinkConfig.default()
fixed_cfg.extra_flags = fixed_cfg.extra_flags.push("--fixed-be")
val fixed_result = link_to_native([bad_smf], out_fixed, fixed_cfg)
expect(fixed_result.is_err()).to_equal(true)
expect(fixed_result.unwrap_err()).to_contain("Invalid SMF magic")

delete_if_exists(bad_smf)
delete_if_exists(out_default)
delete_if_exists(out_fixed)
_ = shell("rmdir '{temp_dir}' 2>/dev/null || true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/linker_wrapper_smf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Linker Wrapper Smf

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
