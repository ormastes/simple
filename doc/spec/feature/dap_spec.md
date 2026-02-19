# Debug Adapter Protocol (DAP) Server Tests

**Feature ID:** #DAP-001 | **Category:** Developer Tools | **Status:** Active

_Source: `test/feature/dap/dap_spec.spl`_

---

## Overview

Tests the Debug Adapter Protocol implementation for the Simple language debugger. Covers
initialization and capability negotiation, breakpoint management (line, conditional, function),
execution control (continue, step over/into/out, pause), stack inspection with scope and
variable retrieval, expression evaluation in stopped context, and debugger events (stopped,
output, terminated).

## Syntax

```simple
val capabilities = {
    "supportsConfigurationDoneRequest": true,
    "supportsBreakpointLocationsRequest": true,
    "supportsEvaluateForHovers": true
}
val breakpoint = {"source": {"path": "/test.spl"}, "line": 10, "verified": true}
val result = {"result": "43", "type": "i64"}
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 19 |

## Test Structure

### DAP - initialization

- ✅ handles initialize request
- ✅ responds with adapter capabilities
### DAP - breakpoints

- ✅ sets line breakpoints
- ✅ sets conditional breakpoints
- ✅ sets function breakpoints
### DAP - execution control

- ✅ starts program execution
- ✅ handles continue request
- ✅ handles step over request
- ✅ handles step into request
- ✅ handles step out request
- ✅ handles pause request
### DAP - stack inspection

- ✅ retrieves stack trace
- ✅ retrieves scopes for frame
- ✅ retrieves variables in scope
### DAP - expression evaluation

- ✅ evaluates expressions in stopped context
- ✅ evaluates watch expressions
### DAP - events

- ✅ sends stopped event on breakpoint hit
- ✅ sends output event for program output
- ✅ sends terminated event when program exits

