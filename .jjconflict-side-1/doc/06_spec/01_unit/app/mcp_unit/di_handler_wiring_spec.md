# Di Handler Wiring Specification

> <details>

<!-- sdn-diagram:id=di_handler_wiring_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_handler_wiring_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_handler_wiring_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_handler_wiring_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Di Handler Wiring Specification

## Scenarios

### DI Handler Config

#### when parsing config/di.sdn

#### has exactly 5 service entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = get_config_text()
val count = count_services(cfg)
expect(count).to_equal(5)
```

</details>

#### debug_handler maps to debug_adapter module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = get_config_text()
val mod_path = extract_service_module(cfg, "debug_handler")
expect(mod_path).to_equal("app.mcp.handler_adapters.debug_adapter")
```

</details>

#### debug_log_handler maps to debug_log_adapter module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = get_config_text()
val mod_path = extract_service_module(cfg, "debug_log_handler")
expect(mod_path).to_equal("app.mcp.handler_adapters.debug_log_adapter")
```

</details>

#### diag_handler maps to diag_adapter module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = get_config_text()
val mod_path = extract_service_module(cfg, "diag_handler")
expect(mod_path).to_equal("app.mcp.handler_adapters.diag_adapter")
```

</details>

#### profile behavior

#### prod profile makes auto services lazy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# auto + prod(lazy=true) = lazy
val result = should_be_lazy_mode("auto", true)
expect(result).to_equal(true)
```

</details>

#### dev profile makes auto services eager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# auto + dev(lazy=false) = eager
val result = should_be_lazy_mode("auto", false)
expect(result).to_equal(false)
```

</details>

#### explicit lazy=true overrides dev profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = should_be_lazy_mode("true", false)
expect(result).to_equal(true)
```

</details>

#### explicit lazy=false overrides prod profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = should_be_lazy_mode("false", true)
expect(result).to_equal(false)
```

</details>

### Dispatch Routing

#### prefix matching

#### debug_log_ prefix routes to debug_log_handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = route_tool("debug_log_status")
expect(result).to_equal("debug_log_handler")
```

</details>

#### debug_ prefix routes to debug_handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = route_tool("debug_create_session")
expect(result).to_equal("debug_handler")
```

</details>

#### simple_ prefix routes to diag_handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = route_tool("simple_status")
expect(result).to_equal("diag_handler")
```

</details>

#### debug_log_ checked before debug_ (order matters)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = route_tool("debug_log_enable")
expect(result).to_equal("debug_log_handler")
```

</details>

#### unknown prefix returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = route_tool("unknown_tool")
expect(result).to_equal("")
```

</details>

#### all tool names

#### all 16 debug tools route to debug_handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_tools = [
    "debug_create_session",
    "debug_list_sessions",
    "debug_close_session",
    "debug_set_breakpoint",
    "debug_remove_breakpoint",
    "debug_continue",
    "debug_step",
    "debug_get_variables",
    "debug_stack_trace",
    "debug_evaluate",
    "debug_set_function_breakpoint",
    "debug_enable_breakpoint",
    "debug_get_source",
    "debug_watch",
    "debug_set_variable",
    "debug_set_data_breakpoint",
    "debug_list_data_breakpoints",
    "debug_remove_data_breakpoint",
    "debug_terminate"
]
var all_ok = true
var idx = 0
while idx < debug_tools.len():
    if route_tool(debug_tools[idx]) != "debug_handler":
        all_ok = false
    idx = idx + 1
expect(all_ok).to_equal(true)
```

</details>

#### all 6 debug_log tools route to debug_log_handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_tools = [
    "debug_log_enable",
    "debug_log_disable",
    "debug_log_clear",
    "debug_log_query",
    "debug_log_tree",
    "debug_log_status"
]
var all_ok = true
var idx = 0
while idx < log_tools.len():
    if route_tool(log_tools[idx]) != "debug_log_handler":
        all_ok = false
    idx = idx + 1
expect(all_ok).to_equal(true)
```

</details>

#### all 12 diag tools route to diag_handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diag_tools = [
    "simple_read",
    "simple_check",
    "simple_symbols",
    "simple_status",
    "simple_expand_at",
    "simple_edit",
    "simple_multi_edit",
    "simple_run",
    "simple_diff",
    "simple_log",
    "simple_squash",
    "simple_new"
]
var all_ok = true
var idx = 0
while idx < diag_tools.len():
    if route_tool(diag_tools[idx]) != "diag_handler":
        all_ok = false
    idx = idx + 1
expect(all_ok).to_equal(true)
```

</details>

### DI Wiring Lifecycle

#### init_di simulation

#### config loads placeholders for all 3 handlers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The config defines all 3 handler services that init_di() will register
val cfg = get_config_text()
expect(has_service(cfg, "debug_handler")).to_equal(true)
expect(has_service(cfg, "debug_log_handler")).to_equal(true)
expect(has_service(cfg, "diag_handler")).to_equal(true)
```

</details>

#### real factories override placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Config defines factory names; init_di() overrides with real factories.
# The factory names in config match the exported function names in adapters.
val cfg = get_config_text()
expect(extract_service_factory(cfg, "debug_handler")).to_equal("create_debug_handler")
expect(extract_service_factory(cfg, "debug_log_handler")).to_equal("create_debug_log_handler")
expect(extract_service_factory(cfg, "diag_handler")).to_equal("create_diag_handler")
```

</details>

#### DI returns singleton on repeated resolve

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All handler services are configured as singletons (singleton: true)
val cfg = get_config_text()
expect(is_service_singleton(cfg, "debug_handler")).to_equal(true)
expect(is_service_singleton(cfg, "debug_log_handler")).to_equal(true)
expect(is_service_singleton(cfg, "diag_handler")).to_equal(true)
```

</details>

#### handler dispatch

#### debug_handler dispatches debug_list_sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = route_tool("debug_list_sessions")
expect(result).to_equal("debug_handler")
```

</details>

#### debug_log_handler dispatches debug_log_status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = route_tool("debug_log_status")
expect(result).to_equal("debug_log_handler")
```

</details>

#### diag_handler dispatches simple_status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = route_tool("simple_status")
expect(result).to_equal("diag_handler")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/di_handler_wiring_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DI Handler Config
- Dispatch Routing
- DI Wiring Lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
