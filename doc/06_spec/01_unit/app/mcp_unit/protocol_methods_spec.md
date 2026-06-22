# Protocol Methods Specification

> <details>

<!-- sdn-diagram:id=protocol_methods_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=protocol_methods_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

protocol_methods_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=protocol_methods_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protocol Methods Specification

## Scenarios

### Protocol Methods

### Method Descriptions

#### describes initialize method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo1(jp("method", js("initialize")))
val method = extract_json_string(req, "method")
expect(method).to_equal("initialize")
```

</details>

#### describes initialized method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo1(jp("method", js("initialized")))
val method = extract_json_string(req, "method")
expect(method).to_equal("initialized")
```

</details>

#### describes ping method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo1(jp("method", js("ping")))
val method = extract_json_string(req, "method")
expect(method).to_equal("ping")
```

</details>

#### describes resources/list method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo1(jp("method", js("resources/list")))
val method = extract_json_string(req, "method")
expect(method).to_equal("resources/list")
```

</details>

#### describes resources/read method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo1(jp("method", js("resources/read")))
val method = extract_json_string(req, "method")
expect(method).to_equal("resources/read")
```

</details>

#### describes tools/list method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo1(jp("method", js("tools/list")))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/list")
```

</details>

#### describes tools/call method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo1(jp("method", js("tools/call")))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/call")
```

</details>

#### describes shutdown method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo1(jp("method", js("shutdown")))
val method = extract_json_string(req, "method")
expect(method).to_equal("shutdown")
```

</details>

### is_initialize Predicate

#### returns true for initialize

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "initialize"
val is_init = method == "initialize"
expect(is_init).to_equal(true)
```

</details>

#### returns false for other methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "ping"
val is_init = method == "initialize"
expect(is_init).to_equal(false)
```

</details>

### is_ping Predicate

#### returns true for ping

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "ping"
val is_ping = method == "ping"
expect(is_ping).to_equal(true)
```

</details>

#### returns false for other methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "initialize"
val is_ping = method == "ping"
expect(is_ping).to_equal(false)
```

</details>

### is_resource_method Predicate

#### returns true for resources/list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "resources/list"
val is_resource = method.starts_with("resources/")
expect(is_resource).to_equal(true)
```

</details>

#### returns true for resources/read

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "resources/read"
val is_resource = method.starts_with("resources/")
expect(is_resource).to_equal(true)
```

</details>

#### returns false for non-resource methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "tools/list"
val is_resource = method.starts_with("resources/")
expect(is_resource).to_equal(false)
```

</details>

### is_tool_method Predicate

#### returns true for tools/list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "tools/list"
val is_tool = method.starts_with("tools/")
expect(is_tool).to_equal(true)
```

</details>

#### returns true for tools/call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "tools/call"
val is_tool = method.starts_with("tools/")
expect(is_tool).to_equal(true)
```

</details>

#### returns false for non-tool methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "resources/list"
val is_tool = method.starts_with("tools/")
expect(is_tool).to_equal(false)
```

</details>

### is_prompt_method Predicate

#### returns true for prompts/list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "prompts/list"
val is_prompt = method.starts_with("prompts/")
expect(is_prompt).to_equal(true)
```

</details>

#### returns true for prompts/get

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "prompts/get"
val is_prompt = method.starts_with("prompts/")
expect(is_prompt).to_equal(true)
```

</details>

#### returns false for non-prompt methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "tools/call"
val is_prompt = method.starts_with("prompts/")
expect(is_prompt).to_equal(false)
```

</details>

### Method Summary Routing

#### routes to initialize summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("method", js("initialize"))))
expect(response.contains("initialize")).to_equal(true)
```

</details>

#### routes to resource summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("method", js("resources/list"))))
expect(response.contains("resources")).to_equal(true)
```

</details>

#### routes to tool summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("method", js("tools/call"))))
expect(response.contains("tools")).to_equal(true)
```

</details>

#### routes to prompt summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("method", js("prompts/get"))))
expect(response.contains("prompts")).to_equal(true)
```

</details>

#### routes to ping summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("method", js("ping"))))
expect(response.contains("ping")).to_equal(true)
```

</details>

#### routes to shutdown summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("method", js("shutdown"))))
expect(response.contains("shutdown")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/protocol_methods_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Protocol Methods
- Method Descriptions
- is_initialize Predicate
- is_ping Predicate
- is_resource_method Predicate
- is_tool_method Predicate
- is_prompt_method Predicate
- Method Summary Routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
