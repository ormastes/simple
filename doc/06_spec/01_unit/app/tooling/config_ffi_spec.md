# Configuration FFI Specification

> Tests for runtime configuration FFI functions that control debugging and macro tracing behavior. These FFI functions allow the interpreter to be configured at runtime for development and diagnostic purposes.

<!-- sdn-diagram:id=config_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=config_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

config_ffi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=config_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Configuration FFI Specification

Tests for runtime configuration FFI functions that control debugging and macro tracing behavior. These FFI functions allow the interpreter to be configured at runtime for development and diagnostic purposes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #XXX |
| Category | Tooling |
| Difficulty | 1/5 |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/config_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for runtime configuration FFI functions that control debugging and
macro tracing behavior. These FFI functions allow the interpreter to be
configured at runtime for development and diagnostic purposes.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Macro Tracing | Enable/disable tracing of macro expansion |
| Debug Mode | Enable/disable runtime debug information |
| FFI Functions | Foreign Function Interface bindings to Rust runtime |
| Flag Independence | Each flag maintained independently |

## Behavior

The configuration FFI module provides:
- Enable/disable macro tracing for debugging macro issues
- Enable/disable debug mode for verbose runtime output
- Query current state of each configuration flag
- Flags are independent and don't affect each other
- Defaults to disabled state

## Examples

```simple
describe "Configuration FFI":
it "enables macro tracing":
rt_set_macro_trace(true)
expect rt_is_macro_trace_enabled() == true
rt_set_macro_trace(false)
```

## Scenarios

### Runtime Configuration FFI

#### should enable and disable macro trace

1. check
2. rt set macro trace
3. check
4. rt set macro trace
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Default should be false
check(not rt_is_macro_trace_enabled())

# Enable it
rt_set_macro_trace(true)
check(rt_is_macro_trace_enabled())

# Disable it
rt_set_macro_trace(false)
check(not rt_is_macro_trace_enabled())
```

</details>

#### should enable and disable debug mode

1. check
2. rt set debug mode
3. check
4. rt set debug mode
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Default should be false
check(not rt_is_debug_mode_enabled())

# Enable it
rt_set_debug_mode(true)
check(rt_is_debug_mode_enabled())

# Disable it
rt_set_debug_mode(false)
check(not rt_is_debug_mode_enabled())
```

</details>

#### should maintain independent flags

1. rt set macro trace
2. rt set debug mode
3. check
4. check
5. rt set macro trace
6. rt set debug mode
7. check
8. check
9. rt set debug mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Set macro trace on, debug mode off
rt_set_macro_trace(true)
rt_set_debug_mode(false)

check(rt_is_macro_trace_enabled())
check(not rt_is_debug_mode_enabled())

# Swap them
rt_set_macro_trace(false)
rt_set_debug_mode(true)

check(not rt_is_macro_trace_enabled())
check(rt_is_debug_mode_enabled())

# Clean up
rt_set_debug_mode(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
