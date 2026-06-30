# MCP Library Schema

> Tests the MCP library schema definitions including tool input schemas, resource templates, and type validation. Verifies that schema objects correctly describe tool parameters and that validation rejects malformed inputs.

<!-- sdn-diagram:id=schema_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=schema_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

schema_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=schema_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Library Schema

Tests the MCP library schema definitions including tool input schemas, resource templates, and type validation. Verifies that schema objects correctly describe tool parameters and that validation rejects malformed inputs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/03_system/feature/lib/mcp/schema_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP library schema definitions including tool input schemas, resource
templates, and type validation. Verifies that schema objects correctly describe
tool parameters and that validation rejects malformed inputs.

## Scenarios

### MCP Library - Schema

#### initializes core schemas

1. init core schemas


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
init_core_schemas()
expect(get_tool_count()).to_be_greater_than(0)
```

</details>

#### gets all tool schemas

1. init core schemas


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
init_core_schemas()
val schemas = get_all_tool_schemas()
expect(schemas).to_start_with("[")
expect(schemas).to_end_with("]")
expect(schemas).to_contain("read_code")
expect(schemas).to_contain("list_files")
```

</details>

#### counts tools

1. init core schemas
   - Expected: count equals `8)  # Core tools defined in init_core_schemas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
init_core_schemas()
val count = get_tool_count()
expect(count).to_equal(8)  # Core tools defined in init_core_schemas
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
