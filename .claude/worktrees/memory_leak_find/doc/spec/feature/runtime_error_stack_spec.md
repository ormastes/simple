# Interpreter Runtime Error Stack Trace

**Feature ID:** #RUNTIME-002 | **Category:** Runtime | **Status:** Active

_Source: `test/feature/interpreter/runtime_error_stack_spec.spl`_

---

## Overview

System test that runs the interpreter CLI against a sample script to verify that runtime errors
include a full call stack section. Validates that when calling nested functions that trigger an
undefined function error, the output includes the "Runtime error" header, the specific error
message, a "Call stack:" section, and frame entries for each function in the call chain
(level1, level2, level3).

## Syntax

```simple
val result = run_interpreter(["src/app/interpreter/main.spl", script])
expect result.exit_code != 0
expect result.stderr.contains("Call stack:")
expect result.stderr.contains("level1")
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### Interpreter Runtime Error Stack Trace

- ✅ includes call stack for nested functions

