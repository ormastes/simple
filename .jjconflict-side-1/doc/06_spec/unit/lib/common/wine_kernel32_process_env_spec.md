# Wine Kernel32 Process Env Specification

> Tests covering Wine KERNEL32 process environment bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Process Env Specification

## Scenarios

### Wine KERNEL32 process environment bridge

#### executes a bounded command-line and environment-block sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a bounded command-line and environment-block sequence
   - Expected: result.ok is true
   - Expected: result.command_line equals `"C:\\Program Files\\hello.exe" --flag`
   - Expected: result.environment_block equals `PATH=C:\\Windows\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a bounded command-line and environment-block sequence")
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

- keeps process environment dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-process-env-sequence-expected:GetCommandLineW`
   - Expected: unsupported.ok is false
   - Expected: unsupported.error equals `bridge-wrong-category:WriteFile`
   - Expected: invalid.ok is false
   - Expected: invalid.error equals `GetCommandLineW:missing-argv0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps process environment dispatch ordered and bounded")
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

- executes bounded process parameter calls
   - Expected: result.ok is true
   - Expected: result.module_file_name equals `C:\\Program Files\\hello.exe`
   - Expected: result.current_directory equals `C:\\Windows`
   - Expected: result.operations equals `GetModuleFileNameW GetCurrentDirectoryW SetCurrentDirectoryW GetCurrentDirect... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes bounded process parameter calls")
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

- executes bounded environment variable calls
   - Expected: result.ok is true
   - Expected: result.value equals `C:\\Windows\\System32`
   - Expected: result.operations equals `SetEnvironmentVariableW GetEnvironmentVariableW ExpandEnvironmentStringsW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes bounded environment variable calls")
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

- keeps environment variable dispatch ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-env-var-sequence-expected:SetEnvironmentVariableW`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps environment variable dispatch ordered and bounded")
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
| Source | `test/unit/lib/common/wine_kernel32_process_env_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 process environment bridge.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `77529c4d89dffb0898cdde788c4847c3dd48a533cbdd91d5e46ad39eadf6aaee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `77529c4d89dffb0898cdde788c4847c3dd48a533cbdd91d5e46ad39eadf6aaee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `77529c4d89dffb0898cdde788c4847c3dd48a533cbdd91d5e46ad39eadf6aaee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/wine_kernel32_process_env_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_kernel32_process_env_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_kernel32_process_env_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_kernel32_process_env_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_kernel32_process_env_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded command-line and environment-block sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_process_env_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps process environment dispatch ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_process_env_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes bounded process parameter calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
