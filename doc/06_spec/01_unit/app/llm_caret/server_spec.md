# Server Specification

> <details>

<!-- sdn-diagram:id=server_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=server_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

server_spec -> std
server_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=server_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Specification

## Scenarios

### Health Endpoint

#### returns ok status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_health_response()
expect(resp).to_contain("\"ok\"")
```

</details>

#### returns service name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_health_response()
expect(resp).to_contain("llm_caret")
```

</details>

#### returns version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_health_response()
expect(resp).to_contain("0.1.0")
```

</details>

### Models Endpoint

#### returns list object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_models_response()
expect(resp).to_contain("\"list\"")
```

</details>

#### includes claude sonnet

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_models_response()
expect(resp).to_contain("claude-sonnet-4-20250514")
```

</details>

#### includes claude opus

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_models_response()
expect(resp).to_contain("claude-opus-4-20250514")
```

</details>

#### includes gpt-4o

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_models_response()
expect(resp).to_contain("gpt-4o")
```

</details>

### Chat Completion Response

#### includes content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_chat_completion_response("Hello!", "gpt-4o", "stop")
expect(resp).to_contain("Hello!")
```

</details>

#### includes model

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_chat_completion_response("Hi", "gpt-4o", "stop")
expect(resp).to_contain("gpt-4o")
```

</details>

#### includes finish reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_chat_completion_response("Hi", "gpt-4o", "stop")
expect(resp).to_contain("stop")
```

</details>

#### has chat.completion object type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_chat_completion_response("Hi", "gpt-4o", "stop")
expect(resp).to_contain("chat.completion")
```

</details>

#### has assistant role

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_chat_completion_response("Hi", "gpt-4o", "stop")
expect(resp).to_contain("assistant")
```

</details>

### Anthropic Response

#### includes text content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_anthropic_response("Hello!", "claude-sonnet-4-20250514", "end_turn")
expect(resp).to_contain("Hello!")
```

</details>

#### has message type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_anthropic_response("Hi", "claude-sonnet-4-20250514", "end_turn")
expect(resp).to_contain("\"message\"")
```

</details>

#### includes stop reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_anthropic_response("Hi", "claude-sonnet-4-20250514", "end_turn")
expect(resp).to_contain("end_turn")
```

</details>

### Error Response

#### includes error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_error_response("not found", 404)
expect(resp).to_contain("not found")
```

</details>

#### includes status code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_error_response("bad request", 400)
expect(resp).to_contain("400")
```

</details>

### Route Handling

#### handles health check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_route("GET", "/v1/health", "")
expect(resp).to_contain("ok")
```

</details>

#### handles models list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_route("GET", "/v1/models", "")
expect(resp).to_contain("list")
```

</details>

#### returns 404 for unknown path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_route("GET", "/unknown", "")
expect(resp).to_contain("not found")
```

</details>

#### returns error for empty chat completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_route("POST", "/v1/chat/completions", "")
expect(resp).to_contain("messages required")
```

</details>

#### returns 501 for valid chat request

- var body = LB
- body = body + Q
- body = body + RB


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var body = LB()
body = body + Q() + "content" + Q() + ":" + Q() + "Hello" + Q()
body = body + RB()
val resp = handle_route("POST", "/v1/chat/completions", body)
expect(resp).to_contain("501")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/server_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Health Endpoint
- Models Endpoint
- Chat Completion Response
- Anthropic Response
- Error Response
- Route Handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
