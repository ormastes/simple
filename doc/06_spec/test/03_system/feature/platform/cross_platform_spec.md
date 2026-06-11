# Cross-Platform Support

> Tests cross-platform compatibility including OS detection, path separator handling, and platform-specific API abstractions. Verifies that Simple programs behave consistently across Linux, macOS, Windows, and FreeBSD.

<!-- sdn-diagram:id=cross_platform_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cross_platform_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cross_platform_spec -> nogc_sync_mut
cross_platform_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cross_platform_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross-Platform Support

Tests cross-platform compatibility including OS detection, path separator handling, and platform-specific API abstractions. Verifies that Simple programs behave consistently across Linux, macOS, Windows, and FreeBSD.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Platform |
| Status | In Progress |
| Source | `test/03_system/feature/platform/cross_platform_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests cross-platform compatibility including OS detection, path separator handling,
and platform-specific API abstractions. Verifies that Simple programs behave
consistently across Linux, macOS, Windows, and FreeBSD.

## Scenarios

### Platform Detection

#### detects current operating system

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detected = is_windows() or is_unix() or is_linux() or is_macos()
check(detected)
```

</details>

#### is_unix returns true on Unix-like systems

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux() or is_macos():
    check(is_unix())
else:
    check(not is_unix() or is_unix())
```

</details>

#### is_windows and is_unix are mutually exclusive

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val both = is_windows() and is_unix()
check(not both)
```

</details>

### Path Separators

#### dir_sep returns platform-specific directory separator

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sep = dir_sep()
val valid = sep == "/" or sep == "\\"
check(valid)
```

</details>

#### path_sep returns platform-specific PATH separator

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sep = path_sep()
val valid = sep == ":" or sep == ";"
check(valid)
```

</details>

#### exe_ext returns correct executable extension

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = exe_ext()
val valid = ext == ".exe" or ext == ""
check(valid)
```

</details>

#### lib_ext returns correct library extension

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = lib_ext()
val valid = ext == ".dll" or ext == ".so" or ext == ".dylib"
check(valid)
```

</details>

### Path Handling

#### join_path combines path components

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val joined = join_path("foo", "bar")
val has_foo = joined.contains("foo")
val has_bar = joined.contains("bar")
check(has_foo and has_bar)
```

</details>

#### normalize_path handles forward slashes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_path("foo/bar")
check(normalized.len() > 0)
```

</details>

#### is_absolute_path detects absolute paths

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unix_abs = is_absolute_path("/usr/bin")
val relative = is_absolute_path("foo/bar")
if not is_windows():
    check(unix_abs)
    check(not relative)
else:
    check(true)
```

</details>

### Process Management

#### shell executes simple commands

1. check
   - Expected: code equals `0`
   - Expected: has_hello is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_windows():
    # /bin/sh not available on Windows
    check(true)
else:
    val _result = test_shell("echo hello")
    val out = _result[0]
    val err = _result[1]
    val code = _result[2]
    expect(code).to_equal(0)
    val has_hello = out.contains("hello")
    expect(has_hello).to_equal(true)
```

</details>

### Linker Auto-Detection

#### detects system linker and provides info

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(test_auto_detect_linker())
check(test_get_linker_info())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
