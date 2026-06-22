# Server Safe Operations Specification

> <details>

<!-- sdn-diagram:id=server_safe_operations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=server_safe_operations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

server_safe_operations_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=server_safe_operations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Safe Operations Specification

## Scenarios

### Server Safe Operations

### safe_read_resource

#### handles validation error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("")
match result:
    case nil: fail("empty resource URI was accepted")
    case err: expect(err.message.contains("empty")).to_equal(true)
```

</details>

#### handles resource not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32001, "Resource not found")
expect(response.contains("Resource not found")).to_equal(true)
```

</details>

#### successfully reads resource

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("content", js("file data"))))
expect(response.contains("file data")).to_equal(true)
```

</details>

#### extracts uri parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("uri", js("file:///test.spl")))
val uri = extract_json_string(params, "uri")
expect(uri).to_equal("file:///test.spl")
```

</details>

#### handles missing uri parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("other", js("value")))
val uri = extract_json_string(params, "uri")
expect(uri).to_equal("")
```

</details>

### safe_execute_tool

#### handles validation error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("")
match result:
    case nil: fail("empty tool name was accepted")
    case err: expect(err.message.contains("empty")).to_equal(true)
```

</details>

#### handles execution error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32002, "Tool execution failed")
expect(response.contains("Tool execution failed")).to_equal(true)
```

</details>

#### successfully executes tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_tool_result("1", "Tool output data")
expect(response.contains("Tool output data")).to_equal(true)
```

</details>

#### extracts name parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("name", js("read_code")))
val name = extract_json_string(params, "name")
expect(name).to_equal("read_code")
```

</details>

#### handles missing name parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("other", js("value")))
val name = extract_json_string(params, "name")
expect(name).to_equal("")
```

</details>

#### extracts arguments parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo2(jp("name", js("read_code")), jp("arguments", js("path=/test.spl")))
val args = extract_json_string(params, "arguments")
expect(args.contains("path")).to_equal(true)
```

</details>

#### handles missing arguments parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("name", js("read_code")))
val args = extract_json_string(params, "arguments")
expect(args).to_equal("")
```

</details>

### Parameter Extraction

#### extracts all required parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo2(jp("name", js("read_code")), jp("uri", js("file:///test.spl")))
val name = extract_json_string(params, "name")
val uri = extract_json_string(params, "uri")
expect(name).to_equal("read_code")
expect(uri).to_equal("file:///test.spl")
```

</details>

#### handles partial parameter set

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("name", js("read_code")))
val name = extract_json_string(params, "name")
val uri = extract_json_string(params, "uri")
expect(name).to_equal("read_code")
expect(uri).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/server_safe_operations_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Server Safe Operations
- safe_read_resource
- safe_execute_tool
- Parameter Extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
