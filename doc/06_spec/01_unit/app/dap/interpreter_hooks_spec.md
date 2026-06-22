# Interpreter Hooks Specification

> <details>

<!-- sdn-diagram:id=interpreter_hooks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_hooks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_hooks_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_hooks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Hooks Specification

## Scenarios

### Interpreter Hooks

#### defines interpreter hook state and breakpoint contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hooks = rt_file_read_text("src/lib/nogc_sync_mut/dap/hooks.spl")

expect(hooks).to_contain("struct BreakpointID:")
expect(hooks).to_contain("enum BreakpointType:")
expect(hooks).to_contain("struct Breakpoint:")
expect(hooks).to_contain("enum ExecutionState:")
expect(hooks).to_contain("struct StackFrame:")
expect(hooks).to_contain("struct Variable:")
expect(hooks).to_contain("struct EvalResult:")
expect(hooks).to_contain("class InterpreterHookContext:")
```

</details>

#### declares runtime hook externs used by the context

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hooks = rt_file_read_text("src/lib/nogc_sync_mut/dap/hooks.spl")

expect(hooks).to_contain("rt_hook_add_breakpoint(file, line, id.id)")
expect(hooks).to_contain("rt_hook_remove_breakpoint(file, line)")
expect(hooks).to_contain("rt_hook_set_breakpoint_enabled(file, line, enabled)")
expect(hooks).to_contain("rt_hook_get_call_depth()")
expect(hooks).to_contain("rt_hook_enable_debugging()")
expect(hooks).to_contain("rt_hook_disable_debugging()")
expect(hooks).to_contain("import app.io.{")
expect(hooks).to_contain("rt_hook_evaluate_expression")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/interpreter_hooks_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Interpreter Hooks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
