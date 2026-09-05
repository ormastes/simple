# Wine Nt Process Env Specification

> Tests covering Wine NT process environment bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Process Env Specification

## Scenarios

### Wine NT process environment bridge

#### lists the modeled process environment and parameter calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists the modeled process environment and parameter calls
   - Expected: calls.len() equals `8`
   - Expected: calls[0] equals `GetCommandLineW`
   - Expected: calls[2] equals `GetCurrentDirectoryW`
   - Expected: calls[4] equals `GetModuleFileNameW`
   - Expected: calls[5] equals `GetEnvironmentVariableW`
   - Expected: calls[7] equals `ExpandEnvironmentStringsW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists the modeled process environment and parameter calls")
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

- blocks environment readiness until POSIX argv/env prerequisites pass
   - Expected: env.ready is false
   - Expected: env.state equals `missing-api-fd-write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks environment readiness until POSIX argv/env prerequisites pass")
val env = wine_nt_process_env_new("fd-open fd-read", _all_async_features(), ["hello.exe"])
expect(env.ready).to_equal(false)
expect(env.state).to_equal("missing-api-fd-write")
```

</details>

#### requires argv0 before exposing a process command line

- requires argv0 before exposing a process command line
   - Expected: env.ready is false
   - Expected: wine_nt_get_command_line_w(env).state equals `missing-argv0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires argv0 before exposing a process command line")
val env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), [])
expect(env.ready).to_equal(false)
expect(wine_nt_get_command_line_w(env).state).to_equal("missing-argv0")
```

</details>

#### formats a modeled command line with simple Windows-style quoting

- formats a modeled command line with simple Windows-style quoting
   - Expected: result.ok is true
   - Expected: result.command_line equals `"C:\\Program Files\\hello.exe" --flag plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats a modeled command line with simple Windows-style quoting")
val env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["C:\\Program Files\\hello.exe", "--flag", "plain"])
val result = wine_nt_get_command_line_w(env)
expect(result.ok).to_equal(true)
expect(result.command_line).to_equal("\"C:\\Program Files\\hello.exe\" --flag plain")
```

</details>

#### formats environment strings as a deterministic block

- formats environment strings as a deterministic block
   - Expected: result.ok is true
   - Expected: result.environment_block equals `PATH=C:\\Windows\nTEMP=C:\\Temp\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats environment strings as a deterministic block")
var env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["hello.exe"])
env = wine_nt_process_env_add(env, "PATH", "C:\\Windows")
env = wine_nt_process_env_add(env, "TEMP", "C:\\Temp")
val result = wine_nt_get_environment_strings_w(env)
expect(result.ok).to_equal(true)
expect(result.environment_block).to_equal("PATH=C:\\Windows\nTEMP=C:\\Temp\n")
```

</details>

#### rejects invalid environment keys

- rejects invalid environment keys
   - Expected: result.ok is false
   - Expected: result.state equals `invalid-env-key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid environment keys")
var env = wine_nt_process_env_new(_all_adapter_apis(), _all_async_features(), ["hello.exe"])
env = wine_nt_process_env_add(env, "", "bad")
val result = wine_nt_get_environment_strings_w(env)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("invalid-env-key")
```

</details>

#### tracks current directory and module filename

- tracks current directory and module filename
   - Expected: module_name.ok is true
   - Expected: module_name.module_file_name equals `C:\\Program Files\\hello.exe`
   - Expected: current.ok is true
   - Expected: current.current_directory equals `C:\\Windows`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks current directory and module filename")
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

- gets, sets, and expands environment variables
   - Expected: windir.ok is true
   - Expected: windir.value equals `C:\\Windows`
   - Expected: expanded.ok is true
   - Expected: expanded.value equals `C:\\Windows\\System32;C:\\Temp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets, sets, and expands environment variables")
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

- rejects invalid and missing environment variable requests
   - Expected: invalid.ready is false
   - Expected: invalid.state equals `invalid-env-key`
   - Expected: wine_nt_get_environment_variable_w(env, "").state equals `invalid-env-key`
   - Expected: wine_nt_get_environment_variable_w(env, "MISSING").state equals `env-var-not-found`
   - Expected: wine_nt_expand_environment_strings_w(env, "").state equals `invalid-template`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid and missing environment variable requests")
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
| Source | `test/unit/lib/common/wine_nt_process_env_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine NT process environment bridge.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e757181199f5324587e32374218709b77b4766b3d6c3e0087b37a43e4fe9727a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e757181199f5324587e32374218709b77b4766b3d6c3e0087b37a43e4fe9727a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e757181199f5324587e32374218709b77b4766b3d6c3e0087b37a43e4fe9727a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/wine_nt_process_env_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_nt_process_env_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_nt_process_env_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_nt_process_env_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_nt_process_env_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_nt_process_env_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists the modeled process environment and parameter calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_nt_process_env_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks environment readiness until POSIX argv/env prerequisites pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_nt_process_env_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires argv0 before exposing a process command line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
