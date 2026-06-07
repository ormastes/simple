# Wine Kernel32 Module Loader Specification

> <details>

<!-- sdn-diagram:id=wine_kernel32_module_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_module_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_module_loader_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_module_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Module Loader Specification

## Scenarios

### Wine KERNEL32 module loader bridge

#### models DLL search order without host filesystem access or DLL execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_plan_dll_search_order(
    "kernel32.dll",
    "C:\\Games",
    "C:\\Users\\Player",
    ["D:\\GameBin", "E:\\Shared"],
    ["kernel32.dll", "ntdll.dll"]
)

expect(result.ok).to_equal(true)
expect(result.search_roots.len()).to_equal(8)
expect(result.search_roots[0]).to_equal("\\KnownDlls")
expect(result.search_roots[1]).to_equal("C:\\Games")
expect(result.search_roots[6]).to_equal("D:\\GameBin")
expect(result.candidate_paths[0]).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.candidate_paths[1]).to_equal("C:\\Games\\kernel32.dll")
expect(result.selected_path).to_equal("\\KnownDlls\\kernel32.dll")
expect(result.evidence).to_contain("dll-search-order-modeled")
expect(result.evidence).to_contain("no-host-filesystem-access")
expect(result.evidence).to_contain("no-dll-entrypoint-executed")
expect(result.status).to_equal("dll-search-order-modeled")
```

</details>

#### uses application directory first for non-KnownDll basenames

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_plan_dll_search_order("gameaudio.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"])

expect(result.ok).to_equal(true)
expect(result.selected_path).to_equal("C:\\Games\\gameaudio.dll")
expect(result.candidate_paths[0]).to_equal("\\KnownDlls\\gameaudio.dll")
expect(result.candidate_paths[1]).to_equal("C:\\Games\\gameaudio.dll")
```

</details>

#### rejects DLL search inputs that would escape the modeled basename lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absolute = wine_kernel32_plan_dll_search_order("C:\\Windows\\System32\\kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"])
expect(absolute.ok).to_equal(false)
expect(absolute.error).to_equal("dll-name-must-be-basename")

val missing_suffix = wine_kernel32_plan_dll_search_order("kernel32", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"])
expect(missing_suffix.ok).to_equal(false)
expect(missing_suffix.error).to_equal("dll-name-must-end-with-dll")
```

</details>

#### executes a bounded module and procedure resolution sequence

1.  table
   - Expected: result.ok is true
   - Expected: result.handle equals `0x120`
   - Expected: result.proc_address equals `0x120000 + 3`
   - Expected: result.operations equals `GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary`
   - Expected: wine_kernel32_get_module_handle_w(result.table, "kernel32.dll").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_module_resolution(
    ["GetModuleHandleW", "LoadLibraryW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "KERNEL32.dll",
    "GetProcAddress"
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x120)
expect(result.proc_address).to_equal(0x120000 + 3)
expect(result.operations).to_equal("GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary")
expect(wine_kernel32_get_module_handle_w(result.table, "kernel32.dll").ok).to_equal(true)
```

</details>

#### executes a bounded LoadLibraryExW module resolution sequence

1.  table
   - Expected: result.ok is true
   - Expected: result.handle equals `0x120`
   - Expected: result.proc_address equals `0x120000 + 3`
   - Expected: result.operations equals `GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_module_resolution_ex(
    ["GetModuleHandleW", "LoadLibraryExW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "kernel32.dll",
    "GetProcAddress",
    0
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x120)
expect(result.proc_address).to_equal(0x120000 + 3)
expect(result.operations).to_equal("GetModuleHandleW LoadLibraryExW GetProcAddress FreeLibrary")
```

</details>

#### keeps module loader dispatch ordered and bounded

1.  table
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-module-loader-sequence-expected:GetModuleHandleW`
2.  table
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:VirtualAlloc`
3.  table
   - Expected: wrong_ex_order.ok is false
   - Expected: wrong_ex_order.error equals `kernel32-module-loader-sequence-expected:LoadLibraryExW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_module_resolution(
    ["LoadLibraryW", "GetModuleHandleW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "kernel32.dll",
    "GetProcAddress"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-module-loader-sequence-expected:GetModuleHandleW")

val wrong_family = wine_kernel32_execute_module_resolution(
    ["GetModuleHandleW", "LoadLibraryW", "VirtualAlloc", "FreeLibrary"],
    _table(),
    "kernel32.dll",
    "GetProcAddress"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:VirtualAlloc")

val wrong_ex_order = wine_kernel32_execute_module_resolution_ex(
    ["GetModuleHandleW", "LoadLibraryW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "kernel32.dll",
    "GetProcAddress",
    0
)
expect(wrong_ex_order.ok).to_equal(false)
expect(wrong_ex_order.error).to_equal("kernel32-module-loader-sequence-expected:LoadLibraryExW")
```

</details>

#### reports missing modules, missing procedures, and invalid handles

1.  table
   - Expected: missing_module.ok is false
   - Expected: missing_module.error equals `GetModuleHandleW:module-not-loaded`
2.  table
   - Expected: missing_proc.ok is false
   - Expected: missing_proc.error equals `GetProcAddress:proc-not-found`
   - Expected: invalid_handle.ok is false
   - Expected: invalid_handle.error equals `invalid-module-handle`
   - Expected: unsupported_flags.ok is false
   - Expected: unsupported_flags.error equals `unsupported-load-flags`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_module = wine_kernel32_execute_module_resolution(
    ["GetModuleHandleW", "LoadLibraryW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "user32.dll",
    "MessageBoxW"
)
expect(missing_module.ok).to_equal(false)
expect(missing_module.error).to_equal("GetModuleHandleW:module-not-loaded")

val missing_proc = wine_kernel32_execute_module_resolution(
    ["GetModuleHandleW", "LoadLibraryW", "GetProcAddress", "FreeLibrary"],
    _table(),
    "kernel32.dll",
    "UnknownProc"
)
expect(missing_proc.ok).to_equal(false)
expect(missing_proc.error).to_equal("GetProcAddress:proc-not-found")

val invalid_handle = wine_kernel32_get_proc_address(_table(), 0x999, "GetProcAddress")
expect(invalid_handle.ok).to_equal(false)
expect(invalid_handle.error).to_equal("invalid-module-handle")

val unsupported_flags = wine_kernel32_load_library_ex_w(_table(), "kernel32.dll", 8)
expect(unsupported_flags.ok).to_equal(false)
expect(unsupported_flags.error).to_equal("unsupported-load-flags")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_module_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 module loader bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
