# Plugin Manifest Specification

> 1. FunctionSpec

<!-- sdn-diagram:id=plugin_manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugin_manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugin_manifest_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugin_manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Plugin Manifest Specification

## Scenarios

### Wrapper generator plugin manifest

#### collects exported functions from free functions and methods

1. FunctionSpec
2. MethodSpec
   - Expected: exported.len() equals `2`
   - Expected: exported[0] equals `rt_regex_new`
   - Expected: exported[1] equals `rt_regex_is_match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = WrapperSpec(
    name: "regex",
    version: "0.1.0",
    lang: "rust",
    link_libs: [],
    search_paths: [],
    cpp_include: "",
    include_paths: [],
    handle_types: [],
    functions: [
        FunctionSpec(name: "new", cpp_fn: "", params: empty_params(), return_type: "i64")
    ],
    methods: [
        MethodSpec(handle: "Regex", name: "is_match", cpp_method: "", params: empty_params(), return_type: "bool")
    ],
    rust_crate: "regex",
    rust_crate_version: "1"
)
val exported = collect_exported_functions(spec)
expect(exported.len()).to_equal(2)
expect(exported[0]).to_equal("rt_regex_new")
expect(exported[1]).to_equal("rt_regex_is_match")
```

</details>

#### emits plugin manifest content with library path and functions

1. FunctionSpec


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = WrapperSpec(
    name: "regex",
    version: "0.1.0",
    lang: "rust",
    link_libs: [],
    search_paths: [],
    cpp_include: "",
    include_paths: [],
    handle_types: [],
    functions: [
        FunctionSpec(name: "new", cpp_fn: "", params: empty_params(), return_type: "i64")
    ],
    methods: [],
    rust_crate: "regex",
    rust_crate_version: "1"
)
val output_dir = scaffold_output_dir(spec, "")
val manifest = emit_plugin_manifest(spec, output_dir)
expect(manifest).to_contain("name: regex")
expect(manifest).to_contain("functions: [rt_regex_new]")
expect(manifest).to_contain("library:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/wrapper_gen/plugin_manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wrapper generator plugin manifest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
