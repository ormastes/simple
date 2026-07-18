# Compiler Import Alias Resolution

> System-level regression check for FR-COMPILER-002. The HIR import resolver must

<!-- sdn-diagram:id=compiler_import_alias_resolution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_import_alias_resolution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_import_alias_resolution_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_import_alias_resolution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Import Alias Resolution

System-level regression check for FR-COMPILER-002. The HIR import resolver must

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/compiler_import_alias_resolution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

System-level regression check for FR-COMPILER-002. The HIR import resolver must
register named imports under the alias when one is present.

## Scenarios

### compiler import alias resolution
_Import aliases must choose the local symbol name used by HIR registration._

#### selects the alias as the local symbol name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(imported_symbol_local_name("CompileOptions", true, "DriverOptions")).to_equal("DriverOptions")
expect(imported_symbol_local_name("CompileOptions", true, "BackendOptions")).to_equal("BackendOptions")
```

</details>

#### keeps the imported name when no alias is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(imported_symbol_local_name("CompileOptions", false, "")).to_equal("CompileOptions")
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
