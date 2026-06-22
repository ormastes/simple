# Simpleos Wine Process Module Loader Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_module_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_module_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_module_loader_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_module_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Module Loader Specification

## Scenarios

### SimpleOS Wine process module loader

### REQ-020: bounded process module resolution

#### should resolve a known KERNEL32 module procedure for a full-Wine process plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val resolution = wine_process_resolve_known_kernel32_module(plan, "kernel32.dll", "GetProcAddress")
expect(resolution.ok).to_equal(true)
expect(resolution.handle).to_equal(0x120)
expect(resolution.proc_address).to_equal(0x120000 + 3)
expect(resolution.operations).to_equal("GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary")
expect(resolution.status).to_equal("module-resolved")
```

</details>

#### should resolve a known KERNEL32 module procedure through LoadLibraryExW

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val resolution = wine_process_resolve_known_kernel32_module_ex(plan, "kernel32.dll", "GetProcAddress", 0)
expect(resolution.ok).to_equal(true)
expect(resolution.handle).to_equal(0x120)
expect(resolution.proc_address).to_equal(0x120000 + 3)
expect(resolution.operations).to_equal("GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary")
expect(resolution.status).to_equal("module-resolved")
```

</details>

#### should block module resolution outside the full-Wine process-session gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\Games"), _hello_gates())
val resolution = wine_process_resolve_known_kernel32_module(plan, "kernel32.dll", "GetProcAddress")
expect(resolution.ok).to_equal(false)
expect(resolution.error).to_equal("unsupported-process-session")
expect(resolution.status).to_equal("blocked")
```

</details>

#### should reject unsupported LoadLibraryExW flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val resolution = wine_process_resolve_known_kernel32_module_ex(plan, "kernel32.dll", "GetProcAddress", 8)
expect(resolution.ok).to_equal(false)
expect(resolution.error).to_equal("LoadLibraryExW:unsupported-load-flags")
expect(resolution.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_module_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine process module loader
- REQ-020: bounded process module resolution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
