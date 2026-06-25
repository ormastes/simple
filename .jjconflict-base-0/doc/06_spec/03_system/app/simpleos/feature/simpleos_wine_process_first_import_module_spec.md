# Simpleos Wine Process First Import Module Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_first_import_module_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_first_import_module_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_first_import_module_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_first_import_module_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process First Import Module Specification

## Scenarios

### SimpleOS Wine first-import module resolution

### REQ-021: first-import module loader bridge

#### should resolve a requested procedure against a validated first import module

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val resolution = wine_process_resolve_first_import_module(plan, wine_known_hello_exe_fixture_bytes(), 8, "GetProcAddress")
expect(resolution.ok).to_equal(true)
expect(resolution.module_name).to_equal("KERNEL32.dll")
expect(resolution.proc_name).to_equal("GetProcAddress")
expect(resolution.operations).to_equal("GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary")
expect(resolution.status).to_equal("module-resolved")
```

</details>

#### should reject first-import module resolution before import inspection passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val resolution = wine_process_resolve_first_import_module(plan, wine_known_hello_exe_fixture_bytes(), 0, "GetProcAddress")
expect(resolution.ok).to_equal(false)
expect(resolution.error).to_equal("invalid-symbol-limit")
expect(resolution.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_first_import_module_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine first-import module resolution
- REQ-021: first-import module loader bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
