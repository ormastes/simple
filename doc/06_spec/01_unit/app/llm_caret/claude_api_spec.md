# Claude Api Specification

> <details>

<!-- sdn-diagram:id=claude_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=claude_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

claude_api_spec -> std
claude_api_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=claude_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Api Specification

## Scenarios

### build_claude_api_body

#### includes model

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_claude_api_body("claude-opus-4-20250514", "[]", "", 0)
expect(body).to_contain("claude-opus-4-20250514")
```

</details>

#### defaults to sonnet model

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_claude_api_body("", "[]", "", 0)
expect(body).to_contain("claude-sonnet-4-20250514")
```

</details>

#### defaults max_tokens to 4096

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_claude_api_body("", "[]", "", 0)
expect(body).to_contain("4096")
```

</details>

#### uses custom max_tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_claude_api_body("", "[]", "", 8192)
expect(body).to_contain("8192")
```

</details>

#### includes system prompt when set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_claude_api_body("", "[]", "Be helpful", 0)
expect(body).to_contain("system")
expect(body).to_contain("Be helpful")
```

</details>

#### omits system prompt when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = build_claude_api_body("", "[]", "", 0)
expect(body).to_contain("model")
# system key should not be present
```

</details>

#### includes messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msgs = build_single_message_json("user", "Hello")
val body = build_claude_api_body("", msgs, "", 0)
expect(body).to_contain("messages")
expect(body).to_contain("Hello")
```

</details>

### build_claude_api_headers

#### includes api key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = build_claude_api_headers("sk-test-123")
expect(h).to_contain("x-api-key: sk-test-123")
```

</details>

#### includes anthropic version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = build_claude_api_headers("key")
expect(h).to_contain("anthropic-version: 2023-06-01")
```

</details>

#### includes content type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = build_claude_api_headers("key")
expect(h).to_contain("content-type: application/json")
```

</details>

### build_single_message_json

#### builds user message

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = build_single_message_json("user", "Hello")
expect(json).to_start_with("[")
expect(json).to_end_with("]")
expect(json).to_contain("\"role\"")
expect(json).to_contain("\"user\"")
expect(json).to_contain("\"content\"")
expect(json).to_contain("\"Hello\"")
```

</details>

#### escapes special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = build_single_message_json("user", "say \"hi\"")
expect(json).to_contain("\\\"hi\\\"")
```

</details>

### parse_claude_api_response

#### parses success response

- var raw = LB
- raw = raw + Q
- raw = raw + Q
- raw = raw + Q
- raw = raw + Q
- raw = raw + Q
- raw = raw + RB
   - Expected: resp.content equals `Hello!`
   - Expected: resp.model equals `claude-sonnet-4-20250514`
   - Expected: resp.stop_reason equals `end_turn`
   - Expected: resp.input_tokens equals `100`
   - Expected: resp.output_tokens equals `50`
   - Expected: resp.is_error is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var raw = LB()
raw = raw + Q() + "text" + Q() + ":" + Q() + "Hello!" + Q() + ","
raw = raw + Q() + "model" + Q() + ":" + Q() + "claude-sonnet-4-20250514" + Q() + ","
raw = raw + Q() + "stop_reason" + Q() + ":" + Q() + "end_turn" + Q() + ","
raw = raw + Q() + "input_tokens" + Q() + ":100,"
raw = raw + Q() + "output_tokens" + Q() + ":50"
raw = raw + RB()
val resp = parse_claude_api_response(raw)
expect(resp.content).to_equal("Hello!")
expect(resp.model).to_equal("claude-sonnet-4-20250514")
expect(resp.stop_reason).to_equal("end_turn")
expect(resp.input_tokens).to_equal(100)
expect(resp.output_tokens).to_equal(50)
expect(resp.is_error).to_equal(false)
```

</details>

#### parses error response

- var raw = LB
- raw = raw + Q
- raw = raw + Q
- raw = raw + RB
   - Expected: resp.is_error is true
   - Expected: resp.error equals `Invalid API key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var raw = LB()
raw = raw + Q() + "type" + Q() + ":" + Q() + "error" + Q() + ","
raw = raw + Q() + "message" + Q() + ":" + Q() + "Invalid API key" + Q()
raw = raw + RB()
val resp = parse_claude_api_response(raw)
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("Invalid API key")
```

</details>

#### handles empty response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = parse_claude_api_response("")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("empty response")
```

</details>

#### defaults stop reason to end_turn

- var raw = LB
- raw = raw + Q
- raw = raw + RB
   - Expected: resp.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var raw = LB()
raw = raw + Q() + "text" + Q() + ":" + Q() + "Hi" + Q()
raw = raw + RB()
val resp = parse_claude_api_response(raw)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

#### preserves raw response

- var raw = LB
- raw = raw + Q
- raw = raw + RB
   - Expected: resp.raw equals `raw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var raw = LB()
raw = raw + Q() + "text" + Q() + ":" + Q() + "test" + Q()
raw = raw + RB()
val resp = parse_claude_api_response(raw)
expect(resp.raw).to_equal(raw)
```

</details>

#### parses zero token counts

- var raw = LB
- raw = raw + Q
- raw = raw + RB
   - Expected: resp.input_tokens equals `0`
   - Expected: resp.output_tokens equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var raw = LB()
raw = raw + Q() + "text" + Q() + ":" + Q() + "Hi" + Q()
raw = raw + RB()
val resp = parse_claude_api_response(raw)
expect(resp.input_tokens).to_equal(0)
expect(resp.output_tokens).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_api_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- build_claude_api_body
- build_claude_api_headers
- build_single_message_json
- parse_claude_api_response

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
