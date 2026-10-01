# Types Specification

> <details>

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Specification

## Scenarios

### Message

#### creates with role and content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = new_message("user", "Hello")
expect(msg.role).to_equal("user")
expect(msg.content).to_equal("Hello")
```

</details>

#### creates user message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = new_user_message("Hi there")
expect(msg.role).to_equal("user")
expect(msg.content).to_equal("Hi there")
```

</details>

#### creates assistant message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = new_assistant_message("I can help")
expect(msg.role).to_equal("assistant")
expect(msg.content).to_equal("I can help")
```

</details>

#### creates system message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = new_system_message("You are helpful")
expect(msg.role).to_equal("system")
expect(msg.content).to_equal("You are helpful")
```

</details>

#### detects user message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = new_user_message("test")
expect(is_user_message(msg)).to_equal(true)
expect(is_assistant_message(msg)).to_equal(false)
```

</details>

#### detects assistant message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = new_assistant_message("test")
expect(is_assistant_message(msg)).to_equal(true)
expect(is_user_message(msg)).to_equal(false)
```

</details>

#### detects system message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = new_system_message("test")
expect(is_system_message(msg)).to_equal(true)
expect(is_user_message(msg)).to_equal(false)
```

</details>

### ChatRequest

#### creates empty request with defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = new_chat_request()
expect(req.provider).to_equal("")
expect(req.model).to_equal("")
expect(req.max_tokens).to_equal(0)
expect(req.stream).to_equal(false)
expect(req.session_id).to_equal("")
```

</details>

#### creates request with prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = new_chat_request_with_prompt("Hello world")
expect(req.messages.len()).to_equal(1)
expect(req.messages[0].role).to_equal("user")
expect(req.messages[0].content).to_equal("Hello world")
```

</details>

#### has empty tools by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = new_chat_request()
expect(req.tools.len()).to_equal(0)
```

</details>

#### has empty extra_args by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = new_chat_request()
expect(req.extra_args.len()).to_equal(0)
```

</details>

#### has negative temperature as unset marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = new_chat_request()
expect(req.temperature < 0.0).to_equal(true)
```

</details>

#### has zero max_turns as unset marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = new_chat_request()
expect(req.max_turns).to_equal(0)
```

</details>

### ChatResponse

#### creates empty response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = new_chat_response()
expect(resp.content).to_equal("")
expect(resp.is_error).to_equal(false)
expect(resp.error).to_equal("")
```

</details>

#### creates error response

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = new_error_response("Connection failed")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("Connection failed")
expect(resp.stop_reason).to_equal("error")
expect(resp.content).to_equal("")
```

</details>

#### creates success response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = new_success_response("Hello!")
expect(resp.content).to_equal("Hello!")
expect(resp.is_error).to_equal(false)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

#### checks response ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = new_success_response("test")
val err = new_error_response("fail")
expect(response_ok(ok)).to_equal(true)
expect(response_ok(err)).to_equal(false)
```

</details>

#### checks response has content

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = new_success_response("hello")
val empty = new_chat_response()
val err = new_error_response("fail")
expect(response_has_content(ok)).to_equal(true)
expect(response_has_content(empty)).to_equal(false)
expect(response_has_content(err)).to_equal(false)
```

</details>

#### has zero token counts by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = new_chat_response()
expect(resp.input_tokens).to_equal(0)
expect(resp.output_tokens).to_equal(0)
```

</details>

### StreamEvent

#### creates generic event

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = new_stream_event("content_block_start", "")
expect(evt.event_type).to_equal("content_block_start")
expect(evt.content).to_equal("")
```

</details>

#### creates text delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = new_text_delta("Hello ")
expect(evt.event_type).to_equal("text_delta")
expect(evt.content).to_equal("Hello ")
```

</details>

#### creates message stop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = new_message_stop("end_turn")
expect(evt.event_type).to_equal("message_stop")
expect(evt.stop_reason).to_equal("end_turn")
expect(evt.content).to_equal("")
```

</details>

#### has empty defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = new_stream_event("test", "data")
expect(evt.session_id).to_equal("")
expect(evt.model).to_equal("")
expect(evt.input_tokens).to_equal(0)
```

</details>

### ProviderConfig

#### creates with provider type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = new_provider_config("claude_cli")
expect(cfg.provider_type).to_equal("claude_cli")
expect(cfg.base_url).to_equal("")
expect(cfg.api_key).to_equal("")
```

</details>

#### has empty defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = new_provider_config("openai")
expect(cfg.model).to_equal("")
expect(cfg.cli_path).to_equal("")
expect(cfg.python_path).to_equal("")
expect(cfg.model_path).to_equal("")
```

</details>

#### has empty extra args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = new_provider_config("local")
expect(cfg.extra_args.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Message
- ChatRequest
- ChatResponse
- StreamEvent
- ProviderConfig

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
