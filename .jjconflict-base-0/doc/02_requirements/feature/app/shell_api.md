# Shell API Specification
*Source:* `test/feature/app/shell_api_spec.spl`

## Overview


**Topics:** stdlib, scripting

## Overview

Shell API provides access to system operations commonly used in shell scripts:
- Process execution with output capture
- File system operations (read, write, list, delete)
- Path manipulation
- Environment variables
- Exit codes and error handling

This API enables writing shell scripts in Simple language, replacing Python and Bash scripts.

## Design Goals

1. **Simple and intuitive** - Match common shell/Python patterns
2. **Safe by default** - Error handling built-in
3. **Cross-platform** - Works on Linux, macOS, Windows
4. **Composable** - Easy to chain operations
5. **Testable** - Can be unit tested unlike shell scripts

## Related Specifications

- **File I/O** - File operations
- **Process Management** - Process control
- **Error Handling** - Result types


