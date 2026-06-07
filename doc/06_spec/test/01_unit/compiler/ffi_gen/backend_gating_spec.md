# FFI generator backend gating specification

> <details>

<!-- sdn-diagram:id=backend_gating_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_gating_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_gating_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_gating_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FFI generator backend gating specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/ffi_gen/backend_gating_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### ffi generator backend gating

#### treats rust as the only supported direct generator backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ffi_backend_supported("rust")).to_equal(true)
expect(ffi_backend_supported("c")).to_equal(false)
expect(ffi_backend_supported("cpp")).to_equal(false)
```

</details>

#### explains the shared-library bridge for unsupported C/C++ backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = LibExternSpec(
    lib_lang: "cpp",
    lib_name: "demo",
    lib_version: "",
    lib_features: [],
    lib_pkg_config: "",
    lib_link: "",
    class_name: "DemoLib",
    methods: [],
    source_file: "demo.spl",
    line_number: 1
)

val message = ffi_backend_not_implemented_message(spec)
expect(message.contains("@Lib(lang: \"cpp\")")).to_equal(true)
expect(message.contains("@export(\"C\")")).to_equal(true)
expect(message.contains("shared-library/header bridge")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
