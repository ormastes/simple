# Wine Kernel32 Path Specification

> 1. wine kernel32 path env default

<!-- sdn-diagram:id=wine_kernel32_path_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_path_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_path_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_path_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Path Specification

## Scenarios

### Wine KERNEL32 path bridge

#### executes bounded Windows, system, temp file, full-path, and search path calls

1. wine kernel32 path env default
   - Expected: result.ok is true
   - Expected: result.windows_directory equals `C:\\Windows`
   - Expected: result.system_directory equals `C:\\Windows\\System32`
   - Expected: result.temp_path equals `C:\\Temp\\`
   - Expected: result.temp_file_name equals `C:\\Temp\\sw0001.tmp`
   - Expected: result.full_path equals `C:\\Program Files\\SimpleWine\\hello.exe`
   - Expected: result.found_path equals `C:\\Program Files\\SimpleWine\\hello.exe`
   - Expected: result.operations equals `GetWindowsDirectoryW GetSystemDirectoryW GetTempPathW GetTempFileNameW GetFul... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_path_lookup(
    ["GetWindowsDirectoryW", "GetSystemDirectoryW", "GetTempPathW", "GetTempFileNameW", "GetFullPathNameW", "SearchPathW"],
    wine_kernel32_path_env_default(),
    "hello.exe",
    "sw"
)

expect(result.ok).to_equal(true)
expect(result.windows_directory).to_equal("C:\\Windows")
expect(result.system_directory).to_equal("C:\\Windows\\System32")
expect(result.temp_path).to_equal("C:\\Temp\\")
expect(result.temp_file_name).to_equal("C:\\Temp\\sw0001.tmp")
expect(result.full_path).to_equal("C:\\Program Files\\SimpleWine\\hello.exe")
expect(result.found_path).to_equal("C:\\Program Files\\SimpleWine\\hello.exe")
expect(result.operations).to_equal("GetWindowsDirectoryW GetSystemDirectoryW GetTempPathW GetTempFileNameW GetFullPathNameW SearchPathW")
```

</details>

#### keeps path dispatch ordered and bounded

1. wine kernel32 path env default
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-path-sequence-expected:GetWindowsDirectoryW`
2. wine kernel32 path env default
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_path_lookup(
    ["SearchPathW", "GetWindowsDirectoryW", "GetSystemDirectoryW", "GetTempPathW", "GetTempFileNameW", "GetFullPathNameW"],
    wine_kernel32_path_env_default(),
    "hello.exe",
    "sw"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-path-sequence-expected:GetWindowsDirectoryW")

val wrong_family = wine_kernel32_execute_path_lookup(
    ["GetWindowsDirectoryW", "GetSystemDirectoryW", "GetTempPathW", "GetTempFileNameW", "GetFullPathNameW", "HeapAlloc"],
    wine_kernel32_path_env_default(),
    "hello.exe",
    "sw"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### reports missing paths and missing search results

1. wine kernel32 path env default
   - Expected: not_found.ok is false
   - Expected: not_found.error equals `SearchPathW:not-found`
   - Expected: not_found.full_path equals `C:\\Program Files\\SimpleWine\\missing.exe`
2. wine kernel32 path env default
   - Expected: invalid.ok is false
   - Expected: invalid.error equals `GetFullPathNameW:invalid-path`
3. wine kernel32 path env default
   - Expected: invalid_prefix.ok is false
   - Expected: invalid_prefix.error equals `GetTempFileNameW:invalid-prefix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_env = WineKernel32PathEnv(
    windows_directory: "C:\\Windows",
    system_directory: "",
    temp_path: "C:\\Temp\\",
    current_directory: "C:\\Program Files\\SimpleWine",
    search_paths: ["C:\\Windows"],
    files: []
)
val missing_system = wine_kernel32_execute_path_lookup(
    ["GetWindowsDirectoryW", "GetSystemDirectoryW", "GetTempPathW", "GetTempFileNameW", "GetFullPathNameW", "SearchPathW"],
    missing_env,
    "hello.exe",
    "sw"
)
expect(missing_system.ok).to_equal(false)
expect(missing_system.error).to_equal("GetSystemDirectoryW:missing-system-directory")

val not_found = wine_kernel32_execute_path_lookup(
    ["GetWindowsDirectoryW", "GetSystemDirectoryW", "GetTempPathW", "GetTempFileNameW", "GetFullPathNameW", "SearchPathW"],
    wine_kernel32_path_env_default(),
    "missing.exe",
    "sw"
)
expect(not_found.ok).to_equal(false)
expect(not_found.error).to_equal("SearchPathW:not-found")
expect(not_found.full_path).to_equal("C:\\Program Files\\SimpleWine\\missing.exe")

val invalid = wine_kernel32_execute_path_lookup(
    ["GetWindowsDirectoryW", "GetSystemDirectoryW", "GetTempPathW", "GetTempFileNameW", "GetFullPathNameW", "SearchPathW"],
    wine_kernel32_path_env_default(),
    "",
    "sw"
)
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("GetFullPathNameW:invalid-path")

val invalid_prefix = wine_kernel32_execute_path_lookup(
    ["GetWindowsDirectoryW", "GetSystemDirectoryW", "GetTempPathW", "GetTempFileNameW", "GetFullPathNameW", "SearchPathW"],
    wine_kernel32_path_env_default(),
    "hello.exe",
    ""
)
expect(invalid_prefix.ok).to_equal(false)
expect(invalid_prefix.error).to_equal("GetTempFileNameW:invalid-prefix")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_path_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 path bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
