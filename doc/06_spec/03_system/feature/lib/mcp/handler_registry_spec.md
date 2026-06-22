# MCP Library Handler Registry

> Tests the MCP handler registry including tool handler registration, lookup by method name, and dispatch to registered handlers. Verifies that the registry correctly maps tool names to handler functions with proper parameter passing.

<!-- sdn-diagram:id=handler_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=handler_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

handler_registry_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=handler_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Library Handler Registry

Tests the MCP handler registry including tool handler registration, lookup by method name, and dispatch to registered handlers. Verifies that the registry correctly maps tool names to handler functions with proper parameter passing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/03_system/feature/lib/mcp/handler_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP handler registry including tool handler registration, lookup by
method name, and dispatch to registered handlers. Verifies that the registry
correctly maps tool names to handler functions with proper parameter passing.

## Scenarios

### MCP Library - Handler Registry

#### registers and finds tool handler

1. register tool handler
   - Expected: found.name equals `test_tool`
   - Expected: found.handler_module equals `app.handlers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = create_tool_handler(
    "test_tool",
    "Test tool",
    "{}",
    "app.handlers",
    "handle_test"
)
register_tool_handler(handler)

val found = find_tool_handler("test_tool")
expect(found.name).to_equal("test_tool")
expect(found.handler_module).to_equal("app.handlers")
```

</details>

#### returns empty handler for unknown tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = find_tool_handler("unknown")
expect(found.name).to_equal("")
```

</details>

#### registers and finds resource handler

1. register resource handler
   - Expected: found.uri_pattern equals `file://`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = create_resource_handler(
    "file://",
    "app.resources",
    "handle_file"
)
register_resource_handler(handler)

val found = find_resource_handler("file:///path/to/file")
expect(found.uri_pattern).to_equal("file://")
```

</details>

#### creates tool handler with schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = create_tool_handler("t1", "Tool 1", "{}", "mod", "func")
expect(handler.name).to_equal("t1")
expect(handler.description).to_equal("Tool 1")
expect(handler.handler_fn).to_equal("func")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
