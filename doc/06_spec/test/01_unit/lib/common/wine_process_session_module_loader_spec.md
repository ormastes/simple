# Wine Process Session Module Loader Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_module_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_module_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_module_loader_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_module_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Module Loader Specification

## Scenarios

### Wine process session module loader

#### resolves a bounded KERNEL32 module procedure for full Wine plans

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_resolve_known_kernel32_module(plan, "kernel32.dll", "GetProcAddress")
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.module_name).to_equal("kernel32.dll")
expect(result.proc_name).to_equal("GetProcAddress")
expect(result.handle).to_equal(0x120)
expect(result.proc_address).to_equal(0x120000 + 3)
expect(result.operations).to_equal("GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary")
expect(result.status).to_equal("module-resolved")
```

</details>

#### resolves a bounded KERNEL32 module procedure through LoadLibraryExW

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_resolve_known_kernel32_module_ex(plan, "kernel32.dll", "GetProcAddress", 0)
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.handle).to_equal(0x120)
expect(result.proc_address).to_equal(0x120000 + 3)
expect(result.operations).to_equal("GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary")
expect(result.status).to_equal("module-resolved")
```

</details>

#### rejects unsupported modules and non-full-Wine sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val missing = wine_process_resolve_known_kernel32_module(plan, "user32.dll", "MessageBoxW")
expect(missing.ok).to_equal(false)
expect(missing.error).to_equal("GetModuleHandleW:module-not-loaded")
expect(missing.status).to_equal("rejected")

val hello = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\Games"), _hello_gates())
val blocked = wine_process_resolve_known_kernel32_module(hello, "kernel32.dll", "GetProcAddress")
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("unsupported-process-session")
expect(blocked.status).to_equal("blocked")
```

</details>

#### rejects unsupported LoadLibraryExW flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_resolve_known_kernel32_module_ex(plan, "kernel32.dll", "GetProcAddress", 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("LoadLibraryExW:unsupported-load-flags")
expect(result.operations).to_equal("GetModuleHandleW")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_module_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session module loader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
