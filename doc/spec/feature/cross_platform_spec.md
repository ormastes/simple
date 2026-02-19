# Cross-Platform Support Tests

**Feature ID:** #PLATFORM-001 | **Category:** Platform | **Status:** In Progress

_Source: `test/feature/platform/cross_platform_spec.spl`_

---

## Overview

Tests platform detection, path handling, and process management across Linux, macOS,
Windows, and FreeBSD. Validates OS detection predicates (is_windows, is_unix, is_linux,
is_macos) and their mutual exclusivity, platform-specific separators (dir_sep, path_sep,
exe_ext, lib_ext), path joining and normalization, absolute path detection, and basic
shell command execution.

## Syntax

```simple
val detected = is_windows() or is_unix() or is_linux() or is_macos()
check(detected)

val sep = dir_sep()
val valid = sep == "/" or sep == "\\"

val joined = join_path("foo", "bar")
check(joined.contains("foo") and joined.contains("bar"))
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### Platform Detection

- ✅ detects current operating system
- ✅ is_unix returns true on Unix-like systems
- ✅ is_windows and is_unix are mutually exclusive
### Path Separators

- ✅ dir_sep returns platform-specific directory separator
- ✅ path_sep returns platform-specific PATH separator
- ✅ exe_ext returns correct executable extension
- ✅ lib_ext returns correct library extension
### Path Handling

- ✅ join_path combines path components
- ✅ normalize_path handles forward slashes
- ✅ is_absolute_path detects absolute paths
### Process Management

- ✅ shell executes simple commands
### Linker Auto-Detection

