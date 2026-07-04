# Simpleos Wine Process Import Descriptor Table Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_import_descriptor_table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_import_descriptor_table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_import_descriptor_table_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_import_descriptor_table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Import Descriptor Table Specification

## Scenarios

### SimpleOS Wine import descriptor table

### REQ-029: bounded multi-DLL import descriptor inspection

#### should inspect multiple full-Wine import descriptors before arbitrary execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_inspect_import_descriptor_table(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.descriptor_count).to_equal(2)
expect(result.dll_names[0]).to_equal("KERNEL32.dll")
expect(result.dll_names[1]).to_equal("USER32.dll")
expect(result.import_count).to_equal(4)
expect(result.evidence).to_contain("full-image-validated")
expect(result.evidence).to_contain("import-descriptor-table-bounded")
expect(result.evidence).to_contain("import-dll-names-resolved")
expect(result.status).to_equal("import-descriptor-table-inspected")
```

</details>

#### should inventory descriptor-qualified thunk records without loading DLLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_inventory_import_descriptor_thunks(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.binding_count).to_equal(4)
expect(result.dll_names[0]).to_equal("KERNEL32.dll")
expect(result.symbols[0]).to_equal("GetStdHandle")
expect(result.dll_names[3]).to_equal("USER32.dll")
expect(result.symbols[3]).to_equal("MessageBoxW")
expect(result.evidence).to_contain("import-descriptor-thunk-bindings-data-backed")
expect(result.evidence).to_contain("import-descriptor-symbol-names-recorded")
expect(result.status).to_equal("import-descriptor-thunks-inventoried")
```

</details>

#### should plan supported import dependencies without loading DLLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_dependencies(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.module_count).to_equal(2)
expect(result.supported_count).to_equal(2)
expect(result.modules[0]).to_equal("KERNEL32.dll")
expect(result.modules[1]).to_equal("USER32.dll")
expect(result.evidence).to_contain("import-dependency-plan-bounded")
expect(result.evidence).to_contain("no-dll-loaded")
expect(result.status).to_equal("import-dependencies-planned")
```

</details>

#### should reject unsupported import dependencies before loading DLLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_dependencies(plan, _known_hello_with_unsupported_import_descriptor(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("unsupported-import-module:ADVAPI32.dll")
expect(result.unsupported_modules[0]).to_equal("ADVAPI32.dll")
expect(result.evidence).to_contain("import-dependency-unsupported-blocked")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine import descriptor table
- REQ-029: bounded multi-DLL import descriptor inspection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
