# Wine Process Session First Import Module Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_first_import_module_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_first_import_module_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_first_import_module_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_first_import_module_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session First Import Module Specification

## Scenarios

### Wine process session first-import module resolution

#### resolves a requested procedure against the first imported KERNEL32 module

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_resolve_first_import_module(plan, wine_known_hello_exe_fixture_bytes(), 8, "GetProcAddress")
expect(result.ok).to_equal(true)
expect(result.module_name).to_equal("KERNEL32.dll")
expect(result.proc_name).to_equal("GetProcAddress")
expect(result.handle).to_equal(0x120)
expect(result.proc_address).to_equal(0x120000 + 3)
expect(result.operations).to_equal("GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary")
expect(result.status).to_equal("module-resolved")
```

</details>

#### keeps first-import module resolution behind import inspection

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_resolve_first_import_module(plan, wine_known_hello_exe_fixture_bytes(), 0, "GetProcAddress")
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_first_import_module_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session first-import module resolution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
