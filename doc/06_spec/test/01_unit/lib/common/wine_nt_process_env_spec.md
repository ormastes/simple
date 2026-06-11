# Wine Nt Process Env Specification

> <details>

<!-- sdn-diagram:id=wine_nt_process_env_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_nt_process_env_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_nt_process_env_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_nt_process_env_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Process Env Specification

## Scenarios

### Wine NT process environment bridge

#### lists the modeled process environment and parameter calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls = wine_nt_process_env_required_calls()
expect(calls.len()).to_equal(8)
expect(calls[0]).to_equal("GetCommandLineW")
expect(calls[2]).to_equal("GetCurrentDirectoryW")
expect(calls[4]).to_equal("GetModuleFileNameW")
expect(calls[5]).to_equal("GetEnvironmentVariableW")
expect(calls[7]).to_equal("ExpandEnvironmentStringsW")
```

</details>

#### blocks environment readiness until POSIX argv/env prerequisites pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wine_nt_process_env_new("fd-open fd-read", _all_async_features(), ["hello.exe"])
expect(env.ready).to_equal(false)
expect(env.state).to_equal("missing-api-fd-write")
```

</details>

#### requires argv0 before exposing a process command line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), [])
expect(env.ready).to_equal(false)
expect(wine_nt_get_command_line_w(env).state).to_equal("missing-argv0")
```

</details>

#### formats a modeled command line with simple Windows-style quoting

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["C:\\Program Files\\hello.exe", "--flag", "plain"])
val result = wine_nt_get_command_line_w(env)
expect(result.ok).to_equal(true)
expect(result.command_line).to_equal("\"C:\\Program Files\\hello.exe\" --flag plain")
```

</details>

#### formats environment strings as a deterministic block

1. var env = wine nt process env new
2. env = wine nt process env add
3. env = wine nt process env add
   - Expected: result.ok is true
   - Expected: result.environment_block equals `PATH=C:\\Windows\nTEMP=C:\\Temp\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["hello.exe"])
env = wine_nt_process_env_add(env, "PATH", "C:\\Windows")
env = wine_nt_process_env_add(env, "TEMP", "C:\\Temp")
val result = wine_nt_get_environment_strings_w(env)
expect(result.ok).to_equal(true)
expect(result.environment_block).to_equal("PATH=C:\\Windows\nTEMP=C:\\Temp\n")
```

</details>

#### rejects invalid environment keys

1. var env = wine nt process env new
2. env = wine nt process env add
   - Expected: result.ok is false
   - Expected: result.state equals `invalid-env-key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["hello.exe"])
env = wine_nt_process_env_add(env, "", "bad")
val result = wine_nt_get_environment_strings_w(env)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("invalid-env-key")
```

</details>

#### tracks current directory and module filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["C:\\Program Files\\hello.exe"])
val module_name = wine_nt_get_module_file_name_w(env)
val changed = wine_nt_set_current_directory_w(env, "C:\\Windows")
val current = wine_nt_get_current_directory_w(changed)

expect(module_name.ok).to_equal(true)
expect(module_name.module_file_name).to_equal("C:\\Program Files\\hello.exe")
expect(current.ok).to_equal(true)
expect(current.current_directory).to_equal("C:\\Windows")
```

</details>

#### gets, sets, and expands environment variables

1. var env = wine nt process env new
2. env = wine nt set environment variable w
3. env = wine nt set environment variable w
   - Expected: windir.ok is true
   - Expected: windir.value equals `C:\\Windows`
   - Expected: expanded.ok is true
   - Expected: expanded.value equals `C:\\Windows\\System32;C:\\Temp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["hello.exe"])
env = wine_nt_set_environment_variable_w(env, "WINDIR", "C:\\Windows")
env = wine_nt_set_environment_variable_w(env, "TEMP", "C:\\Temp")
val windir = wine_nt_get_environment_variable_w(env, "WINDIR")
val expanded = wine_nt_expand_environment_strings_w(env, "%WINDIR%\\System32;%TEMP%")

expect(windir.ok).to_equal(true)
expect(windir.value).to_equal("C:\\Windows")
expect(expanded.ok).to_equal(true)
expect(expanded.value).to_equal("C:\\Windows\\System32;C:\\Temp")
```

</details>

#### rejects invalid and missing environment variable requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["hello.exe"])
val invalid = wine_nt_set_environment_variable_w(env, "", "bad")

expect(invalid.ready).to_equal(false)
expect(invalid.state).to_equal("invalid-env-key")
expect(wine_nt_get_environment_variable_w(env, "").state).to_equal("invalid-env-key")
expect(wine_nt_get_environment_variable_w(env, "MISSING").state).to_equal("env-var-not-found")
expect(wine_nt_expand_environment_strings_w(env, "").state).to_equal("invalid-template")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_nt_process_env_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NT process environment bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
