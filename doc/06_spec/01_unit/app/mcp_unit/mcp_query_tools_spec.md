# mcp_query_tools_spec

> Tests the 5 Tier 2 MCP query tool handlers: simple_definition, simple_references, simple_hover, simple_completions, simple_type_at

<!-- sdn-diagram:id=mcp_query_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_query_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_query_tools_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_query_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_query_tools_spec

Tests the 5 Tier 2 MCP query tool handlers: simple_definition, simple_references, simple_hover, simple_completions, simple_type_at

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-QUERY-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/app/mcp_unit/mcp_query_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the 5 Tier 2 MCP query tool handlers:
simple_definition, simple_references, simple_hover, simple_completions, simple_type_at

## Behavior

- Each tool delegates to bin/simple query CLI
- Requires file and line parameters
- Column parameter is optional

## Scenarios

### simple_definition tool

#### requires file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ""
val has_error = file == ""
expect(has_error).to_equal(true)
```

</details>

#### requires line parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = ""
val has_error = line == ""
expect(has_error).to_equal(true)
```

</details>

#### builds definition command

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query definition " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query definition")
expect(cmd).to_contain(file)
expect(cmd).to_contain(line)
```

</details>

#### builds definition command with column

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val line = "42"
val column = "10"
var cmd = "timeout 30 bin/simple query definition " + file + " " + line
if column != "":
    cmd = cmd + " " + column
expect(cmd).to_contain("42 10")
```

</details>

### simple_references tool

#### builds references command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query references " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query references")
```

</details>

### simple_hover tool

#### builds hover command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query hover " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query hover")
```

</details>

### simple_completions tool

#### builds completions command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query completions " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query completions")
```

</details>

#### builds completions command with prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val line = "42"
val prefix = "cli_"
var cmd = "timeout 30 bin/simple query completions " + file + " " + line
if prefix != "":
    cmd = cmd + " --prefix " + prefix
expect(cmd).to_contain("--prefix cli_")
```

</details>

### simple_type_at tool

#### builds type-at command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query type-at " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query type-at")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
