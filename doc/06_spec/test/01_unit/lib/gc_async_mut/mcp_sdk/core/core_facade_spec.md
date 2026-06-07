# Core Facade Specification

> <details>

<!-- sdn-diagram:id=core_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=core_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

core_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=core_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Core Facade Specification

## Scenarios

### gc_async_mut MCP SDK core facades

#### re-exports JSON and JSON-RPC helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = jo1(jp("name", js("tool")))
val result = jsonrpc_result("1", obj)

expect(obj).to_contain("\"name\":\"tool\"")
expect(result).to_contain("\"id\":\"1\"")
```

</details>

#### re-exports errors and validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = method_not_found("missing")
val json = mcp_error_to_jsonrpc(err)
val limits = default_validation_limits()

expect(json).to_contain(ERR_METHOD_NOT_FOUND())
expect(validate_tool_name(limits, "valid_tool")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/mcp_sdk/core/core_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut MCP SDK core facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
