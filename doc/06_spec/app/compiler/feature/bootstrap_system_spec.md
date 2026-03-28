# Bootstrap System Multi-Platform Tests

**Feature ID:** #BOOTSTRAP-003 | **Category:** Runtime | **Status:** Active

_Source: `test/feature/compiler/bootstrap_system_spec.spl`_

---

## Overview

Tests the multi-platform bootstrap system functionality using the SSpec framework. Validates
platform detection and normalization of architecture/OS names, bootstrap binary capabilities
including script execution, standard library loading, string interpolation, functions, and
classes. Also covers wrapper script behavior, file system operations, platform module information
(separators, extensions), build system integration, error handling, and startup performance.

## Syntax

```simple
val has_platform = is_windows() or is_unix() or is_linux() or is_macos()
check(has_platform)

val dir = dir_sep()
val path = path_sep()
check(dir.len() > 0)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 22 |

## Test Structure

### Bootstrap System

### Platform Detection

- ✅ detects current platform
- ✅ normalizes architecture names
- ✅ normalizes OS names
### Bootstrap Binary

- ✅ executes Simple scripts
- ✅ loads standard library
- ✅ handles string interpolation
- ✅ supports functions
- ✅ supports classes
### Wrapper Script

- ✅ finds bootstrap binary
- ✅ passes arguments correctly
- ✅ handles errors gracefully
### File System

- ✅ can read files
- ✅ can write files
### Platform Module

- ✅ provides platform information
- ✅ provides path separators
- ✅ provides executable and library extensions
### Build System Integration

- ✅ can load build modules
- ✅ supports CLI commands
### Error Handling

- ✅ handles invalid syntax gracefully
- ✅ provides clear error messages
### Performance

- ✅ starts up quickly
- ✅ executes efficiently

