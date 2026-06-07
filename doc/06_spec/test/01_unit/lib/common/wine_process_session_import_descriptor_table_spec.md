# Wine Process Session Import Descriptor Table Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_import_descriptor_table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_import_descriptor_table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_import_descriptor_table_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_import_descriptor_table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Import Descriptor Table Specification

## Scenarios

### Wine process session import descriptor table

#### inspects all bounded import descriptors for a full-Wine image

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_inspect_import_descriptor_table(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.descriptor_count).to_equal(2)
expect(result.dll_names[0]).to_equal("KERNEL32.dll")
expect(result.dll_names[1]).to_equal("USER32.dll")
expect(result.import_count).to_equal(4)
expect(result.evidence).to_contain("import-descriptor-table-valid")
expect(result.evidence).to_contain("import-thunk-tables-bounded")
expect(result.status).to_equal("import-descriptor-table-inspected")
```

</details>

#### rejects descriptor tables beyond the caller supplied bound

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_inspect_import_descriptor_table(plan, _known_hello_with_second_import_descriptor(), 1, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-descriptor-limit-exceeded")
expect(result.status).to_equal("rejected")
```

</details>

#### inventories descriptor-qualified thunk bindings before loading DLLs

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
expect(result.evidence).to_contain("import-descriptor-thunk-rvas-recorded")
expect(result.status).to_equal("import-descriptor-thunks-inventoried")
```

</details>

#### plans supported import dependencies without loading DLLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_dependencies(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.module_count).to_equal(2)
expect(result.supported_count).to_equal(2)
expect(result.unsupported_count).to_equal(0)
expect(result.modules[0]).to_equal("KERNEL32.dll")
expect(result.modules[1]).to_equal("USER32.dll")
expect(result.evidence).to_contain("import-dependency-modules-supported")
expect(result.evidence).to_contain("no-dll-loaded")
expect(result.evidence).to_contain("no-import-bound")
expect(result.status).to_equal("import-dependencies-planned")
```

</details>

#### rejects unsupported import dependencies before loader work

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_dependencies(plan, _known_hello_with_unsupported_import_descriptor(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("unsupported-import-module:ADVAPI32.dll")
expect(result.module_count).to_equal(2)
expect(result.unsupported_count).to_equal(1)
expect(result.unsupported_modules[0]).to_equal("ADVAPI32.dll")
expect(result.evidence).to_contain("import-dependency-unsupported-blocked")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_import_descriptor_table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session import descriptor table

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
