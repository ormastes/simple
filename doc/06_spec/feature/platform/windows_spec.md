# Windows Platform

> Tests Windows-specific platform features using a local harness that preserves test intent without depending on Windows-only modules. Verifies path handling, executable extensions, and MSVC/MinGW toolchain detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Windows Platform

Tests Windows-specific platform features using a local harness that preserves test intent without depending on Windows-only modules. Verifies path handling, executable extensions, and MSVC/MinGW toolchain detection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Platform |
| Status | In Progress |
| Source | `test/feature/platform/windows_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests Windows-specific platform features using a local harness that preserves
test intent without depending on Windows-only modules. Verifies path handling,
executable extensions, and MSVC/MinGW toolchain detection.

## Scenarios

### Windows Path Normalization

#### converts forward slashes to backslashes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts forward slashes to backslashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts forward slashes to backslashes")
check(normalize_windows_path("C:/Users/foo") == "C:\\Users\\foo")
```

</details>

#### handles drive letters correctly

- handles drive letters correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles drive letters correctly")
check(normalize_windows_path("D:/data/bin") == "D:\\data\\bin")
```

</details>

#### converts UNC paths correctly

- converts UNC paths correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts UNC paths correctly")
check(normalize_windows_path("//server/share") == "\\\\server\\share")
```

</details>

#### handles mixed slashes

- handles mixed slashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles mixed slashes")
check(normalize_windows_path("C:/Users\\Alice/Documents") == "C:\\Users\\Alice\\Documents")
```

</details>

### MinGW Path Support

#### detects MinGW-style paths

- detects MinGW-style paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects MinGW-style paths")
check(is_mingw_path("/c/Users/Alice"))
```

</details>

#### rejects non-MinGW paths

- rejects non-MinGW paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects non-MinGW paths")
check(not is_mingw_path("C:/Users/Alice"))
```

</details>

#### converts MinGW paths to Windows format

- converts MinGW paths to Windows format


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts MinGW paths to Windows format")
check(mingw_to_windows("/c/Users/Alice") == "C:\\Users\\Alice")
```

</details>

#### converts Windows paths to MinGW format

- converts Windows paths to MinGW format


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts Windows paths to MinGW format")
check(windows_to_mingw("C:\\Users\\Alice") == "/c/Users/Alice")
```

</details>

#### treats MinGW paths as absolute

- treats MinGW paths as absolute


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("treats MinGW paths as absolute")
check(is_absolute_windows("/c/Users/Alice"))
```

</details>

### Windows Separators

#### dir_sep returns backslash

- dir_sep returns backslash


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dir_sep returns backslash")
check(dir_sep() == "\\")
```

</details>

#### path_sep returns semicolon

- path_sep returns semicolon


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("path_sep returns semicolon")
check(path_sep() == ";")
```

</details>

#### exe_ext returns .exe

- exe_ext returns .exe


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("exe_ext returns .exe")
check(exe_ext() == ".exe")
```

</details>

### Windows Command Resolution

#### adds .exe extension to commands without extension

- adds .exe extension to commands without extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds .exe extension to commands without extension")
check(resolve_command("myapp") == "myapp.exe")
```

</details>

#### preserves commands with .exe extension

- preserves commands with .exe extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves commands with .exe extension")
check(resolve_command("myapp.exe") == "myapp.exe")
```

</details>

#### handles .bat and .cmd files

- handles .bat and .cmd files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles .bat and .cmd files")
check(resolve_command("setup.bat") == "setup.bat")
check(resolve_command("setup.cmd") == "setup.cmd")
```

</details>

#### preserves absolute paths

- preserves absolute paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves absolute paths")
check(resolve_command("C:\\tools\\myapp") == "C:\\tools\\myapp")
```

</details>

### Windows Path Class

#### joins paths with backslashes

- joins paths with backslashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins paths with backslashes")
val path = WindowsPath.new("C:\\Users")
check(path.join("Alice") == "C:\\Users\\Alice")
```

</details>

#### extracts file names from Windows paths

- extracts file names from Windows paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("extracts file names from Windows paths")
val path = WindowsPath.new("C:\\Users\\Alice\\notes.txt")
check(path.file_name() == "notes.txt")
```

</details>

#### handles UNC paths in Path class

- handles UNC paths in Path class


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles UNC paths in Path class")
val path = WindowsPath.new("\\\\server\\share")
check(path.is_absolute())
```

</details>

### Windows Shell Execution

#### executes cmd.exe commands

- executes cmd.exe commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("executes cmd.exe commands")
val result = local_shell("cmd.exe /C echo ok")
check(result.exit_code == 0)
```

</details>

#### captures stdout correctly

- captures stdout correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("captures stdout correctly")
val result = local_shell("cmd.exe /C echo ok")
check(result.stdout == "ok")
```

</details>

### MSVC Linker Detection

#### can check if MSVC is available

- can check if MSVC is available


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can check if MSVC is available")
check(detect_windows_linker("toolchain-msvc") == "msvc")
```

</details>

#### can check if lld-link is available

- can check if lld-link is available


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can check if lld-link is available")
check(detect_windows_linker("toolchain-lld-link") == "lld-link")
```

</details>

#### Windows linker type has string representation

- Windows linker type has string representation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Windows linker type has string representation")
check(detect_windows_linker("toolchain-msvc") == "msvc")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `48fed0cb2f57aff22efa3cd321cec84fcda937620d2c40de1feb66b98bc7d610`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48fed0cb2f57aff22efa3cd321cec84fcda937620d2c40de1feb66b98bc7d610`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48fed0cb2f57aff22efa3cd321cec84fcda937620d2c40de1feb66b98bc7d610`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/feature/platform/windows_spec.spl
mirror: doc/06_spec/feature/platform/windows_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/platform/windows_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/platform/windows_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/platform/windows_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts forward slashes to backslashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/platform/windows_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles drive letters correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/platform/windows_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts UNC paths correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/platform/windows_spec.spl:223:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can check if MSVC is available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/feature/platform/windows_spec.spl:228:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can check if lld-link is available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
