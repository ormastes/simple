# Openai Api Specification

> <details>

<!-- sdn-diagram:id=openai_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=openai_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

openai_api_spec -> std
openai_api_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=openai_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Openai Api Specification

## Scenarios

### build_openai_body

#### includes model

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_openai_body("gpt-4-turbo", "[]", 0, -1.0)
expect(body).to_contain("gpt-4-turbo")
```

</details>

#### defaults to gpt-4o

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_openai_body("", "[]", 0, -1.0)
expect(body).to_contain("gpt-4o")
```

</details>

#### includes messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msgs = build_openai_messages_json(["user"], ["Hello"])
val body = build_openai_body("", msgs, 0, -1.0)
expect(body).to_contain("messages")
expect(body).to_contain("Hello")
```

</details>

#### includes max_tokens when set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_openai_body("", "[]", 2048, -1.0)
expect(body).to_contain("2048")
```

</details>

#### omits max_tokens when zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_openai_body("", "[]", 0, -1.0)
expect(body).to_contain("model")
```

</details>

#### includes temperature when non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_openai_body("", "[]", 0, 0.7)
expect(body).to_contain("temperature")
```

</details>

#### omits temperature when negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_openai_body("", "[]", 0, -1.0)
expect(body).to_contain("model")
```

</details>

### build_openai_headers

#### includes bearer token

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = build_openai_headers("sk-test")
expect(h).to_contain("Authorization: Bearer sk-test")
```

</details>

#### includes content type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = build_openai_headers("key")
expect(h).to_contain("Content-Type: application/json")
```

</details>

### build_openai_messages_json

#### builds single message

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = build_openai_messages_json(["user"], ["Hello"])
expect(json).to_start_with("[")
expect(json).to_end_with("]")
expect(json).to_contain("user")
expect(json).to_contain("Hello")
```

</details>

#### builds multi-turn conversation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = build_openai_messages_json(["user", "assistant", "user"], ["Hi", "Hello!", "How are you?"])
expect(json).to_contain("user")
expect(json).to_contain("assistant")
expect(json).to_contain("Hi")
expect(json).to_contain("Hello!")
expect(json).to_contain("How are you?")
```

</details>

### parse_openai_response

#### parses success response

- jp
- jp
- jp
- jp
- jp
- jp
   - Expected: resp.content equals `Hi there!`
   - Expected: resp.model equals `gpt-4o`
   - Expected: resp.finish_reason equals `stop`
   - Expected: resp.prompt_tokens equals `50`
   - Expected: resp.completion_tokens equals `25`
   - Expected: resp.total_tokens equals `75`
   - Expected: resp.is_error is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = jo6(
    jp("content", js("Hi there!")),
    jp("model", js("gpt-4o")),
    jp("finish_reason", js("stop")),
    jp("prompt_tokens", "50"),
    jp("completion_tokens", "25"),
    jp("total_tokens", "75")
)
val resp = parse_openai_response(raw)
expect(resp.content).to_equal("Hi there!")
expect(resp.model).to_equal("gpt-4o")
expect(resp.finish_reason).to_equal("stop")
expect(resp.prompt_tokens).to_equal(50)
expect(resp.completion_tokens).to_equal(25)
expect(resp.total_tokens).to_equal(75)
expect(resp.is_error).to_equal(false)
```

</details>

#### handles empty response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = parse_openai_response("")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("empty response")
```

</details>

#### defaults finish reason to stop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = jo1(jp("content", js("Hello")))
val resp = parse_openai_response(raw)
expect(resp.finish_reason).to_equal("stop")
```

</details>

#### preserves raw response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = jo1(jp("content", js("test")))
val resp = parse_openai_response(raw)
expect(resp.raw).to_equal(raw)
```

</details>

#### handles zero token counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = jo1(jp("content", js("Hi")))
val resp = parse_openai_response(raw)
expect(resp.prompt_tokens).to_equal(0)
expect(resp.completion_tokens).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/openai_api_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- build_openai_body
- build_openai_headers
- build_openai_messages_json
- parse_openai_response

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
