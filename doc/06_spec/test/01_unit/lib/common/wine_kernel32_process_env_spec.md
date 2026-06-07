# Wine Kernel32 Process Env Specification

> 1. var env = wine nt process env new

<!-- sdn-diagram:id=wine_kernel32_process_env_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_process_env_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_process_env_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_process_env_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Process Env Specification

## Scenarios

### Wine KERNEL32 process environment bridge

#### executes a bounded command-line and environment-block sequence

1. var env = wine nt process env new
2. env = wine nt process env add
   - Expected: result.ok is true
   - Expected: result.command_line equals `"C:\\Program Files\\hello.exe" --flag`
   - Expected: result.environment_block equals `PATH=C:\\Windows\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["C:\\Program Files\\hello.exe", "--flag"])
env = wine_nt_process_env_add(env, "PATH", "C:\\Windows")
val result = wine_kernel32_execute_process_env(["GetCommandLineW", "GetEnvironmentStringsW"], env)
expect(result.ok).to_equal(true)
expect(result.command_line).to_equal("\"C:\\Program Files\\hello.exe\" --flag")
expect(result.environment_block).to_equal("PATH=C:\\Windows\n")
expect(result.operations).to_contain("GetCommandLineW")
expect(result.operations).to_contain("GetEnvironmentStringsW")
```

</details>

#### keeps process environment dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["hello.exe"])
val out_of_order = wine_kernel32_execute_process_env(["GetEnvironmentStringsW", "GetCommandLineW"], env)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-process-env-sequence-expected:GetCommandLineW")

val unsupported = wine_kernel32_execute_process_env(["GetCommandLineW", "WriteFile"], env)
expect(unsupported.ok).to_equal(false)
expect(unsupported.error).to_equal("bridge-wrong-category:WriteFile")

val invalid = wine_kernel32_execute_process_env(["GetCommandLineW", "GetEnvironmentStringsW"], wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), []))
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("GetCommandLineW:missing-argv0")
```

</details>

#### executes bounded process parameter calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["C:\\Program Files\\hello.exe"])
val result = wine_kernel32_execute_process_parameters(
    ["GetModuleFileNameW", "GetCurrentDirectoryW", "SetCurrentDirectoryW", "GetCurrentDirectoryW"],
    env,
    "C:\\Windows"
)
expect(result.ok).to_equal(true)
expect(result.module_file_name).to_equal("C:\\Program Files\\hello.exe")
expect(result.current_directory).to_equal("C:\\Windows")
expect(result.operations).to_equal("GetModuleFileNameW GetCurrentDirectoryW SetCurrentDirectoryW GetCurrentDirectoryW")
```

</details>

#### executes bounded environment variable calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["hello.exe"])
val result = wine_kernel32_execute_environment_variable(
    ["SetEnvironmentVariableW", "GetEnvironmentVariableW", "ExpandEnvironmentStringsW"],
    env,
    "WINDIR",
    "C:\\Windows",
    "%WINDIR%\\System32"
)

expect(result.ok).to_equal(true)
expect(result.value).to_equal("C:\\Windows\\System32")
expect(result.operations).to_equal("SetEnvironmentVariableW GetEnvironmentVariableW ExpandEnvironmentStringsW")
```

</details>

#### keeps environment variable dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["hello.exe"])
val out_of_order = wine_kernel32_execute_environment_variable(
    ["GetEnvironmentVariableW", "SetEnvironmentVariableW", "ExpandEnvironmentStringsW"],
    env,
    "WINDIR",
    "C:\\Windows",
    "%WINDIR%"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-env-var-sequence-expected:SetEnvironmentVariableW")

val wrong_family = wine_kernel32_execute_environment_variable(
    ["SetEnvironmentVariableW", "GetEnvironmentVariableW", "HeapAlloc"],
    env,
    "WINDIR",
    "C:\\Windows",
    "%WINDIR%"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_process_env_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 process environment bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
