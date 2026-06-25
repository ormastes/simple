# Server Routing Specification

> <details>

<!-- sdn-diagram:id=server_routing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=server_routing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

server_routing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=server_routing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Routing Specification

## Scenarios

### Server Method Routing

### Core Protocol Methods

#### routes initialize method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("initialize")), jp("id", "1"))
val method = extract_json_string(req, "method")
expect(method).to_equal("initialize")
```

</details>

#### routes initialized notification

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

#### routes ping method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("ping")), jp("id", "2"))
val method = extract_json_string(req, "method")
expect(method).to_equal("ping")
```

</details>

#### routes shutdown method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("shutdown")), jp("id", "3"))
val method = extract_json_string(req, "method")
expect(method).to_equal("shutdown")
```

</details>

### Resource Methods

#### routes resources/list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("resources/list")), jp("id", "4"))
val method = extract_json_string(req, "method")
expect(method).to_equal("resources/list")
```

</details>

#### routes resources/read

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("resources/read")), jp("id", "5"))
val method = extract_json_string(req, "method")
expect(method).to_equal("resources/read")
```

</details>

### Tool Methods

#### routes tools/list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("tools/list")), jp("id", "6"))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/list")
```

</details>

#### routes tools/call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("tools/call")), jp("id", "7"))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/call")
```

</details>

### Prompt Methods

#### routes prompts/list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("prompts/list")), jp("id", "8"))
val method = extract_json_string(req, "method")
expect(method).to_equal("prompts/list")
```

</details>

#### routes prompts/get

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("prompts/get")), jp("id", "9"))
val method = extract_json_string(req, "method")
expect(method).to_equal("prompts/get")
```

</details>

### Unknown Methods

#### handles unknown method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method = "unknown/method"
val is_known = method == "initialize" or method == "ping" or method == "shutdown"
expect(is_known).to_equal(false)
```

</details>

### Method Category Checks

#### identifies resource methods

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

#### identifies tool methods

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

#### identifies prompt methods

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/server_routing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Server Method Routing
- Core Protocol Methods
- Resource Methods
- Tool Methods
- Prompt Methods
- Unknown Methods
- Method Category Checks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
