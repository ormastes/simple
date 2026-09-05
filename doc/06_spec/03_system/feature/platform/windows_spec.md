# Windows Platform

> Tests Windows-specific platform features using a local harness that preserves test intent without depending on Windows-only modules. Verifies path handling, executable extensions, and MSVC/MinGW toolchain detection.

<!-- sdn-diagram:id=windows_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=windows_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

windows_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=windows_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/platform/windows_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests Windows-specific platform features using a local harness that preserves
test intent without depending on Windows-only modules. Verifies path handling,
executable extensions, and MSVC/MinGW toolchain detection.

## Scenarios

### Windows Path Normalization

#### converts forward slashes to backslashes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(normalize_windows_path("C:/Users/foo") == "C:\\Users\\foo")
```

</details>

#### handles drive letters correctly

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(normalize_windows_path("D:/data/bin") == "D:\\data\\bin")
```

</details>

#### converts UNC paths correctly

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(normalize_windows_path("//server/share") == "\\\\server\\share")
```

</details>

#### handles mixed slashes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(normalize_windows_path("C:/Users\\Alice/Documents") == "C:\\Users\\Alice\\Documents")
```

</details>

### MinGW Path Support

#### detects MinGW-style paths

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(is_mingw_path("/c/Users/Alice"))
```

</details>

#### rejects non-MinGW paths

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not is_mingw_path("C:/Users/Alice"))
```

</details>

#### converts MinGW paths to Windows format

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(mingw_to_windows("/c/Users/Alice") == "C:\\Users\\Alice")
```

</details>

#### converts Windows paths to MinGW format

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(windows_to_mingw("C:\\Users\\Alice") == "/c/Users/Alice")
```

</details>

#### treats MinGW paths as absolute

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(is_absolute_windows("/c/Users/Alice"))
```

</details>

### Windows Separators

#### dir_sep returns backslash

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(dir_sep() == "\\")
```

</details>

#### path_sep returns semicolon

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(path_sep() == ";")
```

</details>

#### exe_ext returns .exe

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(exe_ext() == ".exe")
```

</details>

### Windows Command Resolution

#### adds .exe extension to commands without extension

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(resolve_command("myapp") == "myapp.exe")
```

</details>

#### preserves commands with .exe extension

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(resolve_command("myapp.exe") == "myapp.exe")
```

</details>

#### handles .bat and .cmd files

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(resolve_command("setup.bat") == "setup.bat")
check(resolve_command("setup.cmd") == "setup.cmd")
```

</details>

#### preserves absolute paths

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(resolve_command("C:\\tools\\myapp") == "C:\\tools\\myapp")
```

</details>

### Windows Path Class

#### joins paths with backslashes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = WindowsPath.new("C:\\Users")
check(path.join("Alice") == "C:\\Users\\Alice")
```

</details>

#### extracts file names from Windows paths

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = WindowsPath.new("C:\\Users\\Alice\\notes.txt")
check(path.file_name() == "notes.txt")
```

</details>

#### handles UNC paths in Path class

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = WindowsPath.new("\\\\server\\share")
check(path.is_absolute())
```

</details>

### Windows Shell Execution

#### executes cmd.exe commands

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = local_shell("cmd.exe /C echo ok")
check(result.exit_code == 0)
```

</details>

#### captures stdout correctly

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = local_shell("cmd.exe /C echo ok")
check(result.stdout == "ok")
```

</details>

### MSVC Linker Detection

#### can check if MSVC is available

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(detect_windows_linker("toolchain-msvc") == "msvc")
```

</details>

#### can check if lld-link is available

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(detect_windows_linker("toolchain-lld-link") == "lld-link")
```

</details>

#### Windows linker type has string representation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
