# Interpreter Runtime Error Stack Trace

> Tests runtime error stack trace generation in the interpreter including error message formatting, source location reporting, and call chain display. Verifies that runtime errors produce actionable diagnostics with accurate file and line info.

<!-- sdn-diagram:id=runtime_error_stack_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runtime_error_stack_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runtime_error_stack_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runtime_error_stack_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Runtime Error Stack Trace

Tests runtime error stack trace generation in the interpreter including error message formatting, source location reporting, and call chain display. Verifies that runtime errors produce actionable diagnostics with accurate file and line info.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/runtime_error_stack_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests runtime error stack trace generation in the interpreter including error
message formatting, source location reporting, and call chain display. Verifies
that runtime errors produce actionable diagnostics with accurate file and line info.

## Scenarios

### Interpreter Runtime Error Stack Trace

#### includes call stack for nested functions

1. expect result stderr contains
2. expect result stderr contains
3. expect result stderr contains
4. expect result stderr contains
5. expect result stderr contains
6. expect result stderr contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "test/system/interpreter/sample/runtime_error_stack.spl"
val result = run_interpreter(["src/app/interpreter/main.spl", script])
expect result.exit_code != 0
expect result.stderr.contains("Runtime error")
expect result.stderr.contains("undefined function 'missing_fn'")
expect result.stderr.contains("Call stack:")
expect result.stderr.contains("level1")
expect result.stderr.contains("level2")
expect result.stderr.contains("level3")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
