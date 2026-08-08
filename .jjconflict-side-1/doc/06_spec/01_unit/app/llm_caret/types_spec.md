# LLM Caret Types Unit Spec

> Source-synchronized unit manual. The current self-hosted SSpec runner is
> blocked before trustworthy scenario execution, so this document records
> 14 active scenarios and 0 executed scenarios.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 14 | 14 | 0 | 0 | 0 |

**Executable source:** `test/01_unit/app/llm_caret/types_spec.spl`

## should preserve an explicit role and content

**Group:** Message

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production message with an explicit role")
val msg: Message = new_message("tool", "result")
expect(msg.role).to_equal("tool")
expect(msg.content).to_equal("result")
```

</details>

## should construct and classify a user message

**Group:** Message

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production user message")
val msg = new_user_message("Hi there")
expect(msg.role).to_equal("user")
expect(msg.content).to_equal("Hi there")
expect(is_user_message(msg)).to_be(true)
expect(is_assistant_message(msg)).to_be(false)
expect(is_system_message(msg)).to_be(false)
```

</details>

## should construct and classify an assistant message

**Group:** Message

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production assistant message")
val msg = new_assistant_message("I can help")
expect(msg.role).to_equal("assistant")
expect(msg.content).to_equal("I can help")
expect(is_user_message(msg)).to_be(false)
expect(is_assistant_message(msg)).to_be(true)
expect(is_system_message(msg)).to_be(false)
```

</details>

## should construct and classify a system message

**Group:** Message

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production system message")
val msg = new_system_message("You are helpful")
expect(msg.role).to_equal("system")
expect(msg.content).to_equal("You are helpful")
expect(is_user_message(msg)).to_be(false)
expect(is_assistant_message(msg)).to_be(false)
expect(is_system_message(msg)).to_be(true)
```

</details>

## should construct every empty request default

**Group:** ChatRequest

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production request without a prompt")
val req: ChatRequest = new_chat_request()
expect(req.provider).to_equal("")
expect(req.model).to_equal("")
expect(req.messages.len()).to_equal(0)
expect(req.system_prompt).to_equal("")
expect(req.max_tokens).to_equal(0)
expect(req.temperature).to_be_less_than(0.0)
expect(req.session_id).to_equal("")
expect(req.max_turns).to_equal(0)
expect(req.stream).to_be(false)
expect(req.json_schema).to_equal("")
expect(req.tools.len()).to_equal(0)
expect(req.extra_args.len()).to_equal(0)
```

</details>

## should construct a prompt request with one user message

**Group:** ChatRequest

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production request from a prompt")
val req = new_chat_request_with_prompt("Hello world")
expect(req.messages.len()).to_equal(1)
expect(req.messages[0].role).to_equal("user")
expect(req.messages[0].content).to_equal("Hello world")
expect(req.temperature).to_be_less_than(0.0)
expect(req.stream).to_be(false)
```

</details>

## should construct every empty response default

**Group:** ChatResponse

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production empty response")
val resp: ChatResponse = new_chat_response()
expect(resp.content).to_equal("")
expect(resp.model).to_equal("")
expect(resp.provider).to_equal("")
expect(resp.session_id).to_equal("")
expect(resp.stop_reason).to_equal("")
expect(resp.input_tokens).to_equal(0)
expect(resp.output_tokens).to_equal(0)
expect(resp.error).to_equal("")
expect(resp.is_error).to_be(false)
expect(resp.raw).to_equal("")
expect(response_ok(resp)).to_be(true)
expect(response_has_content(resp)).to_be(false)
```

</details>

## should construct an error response and reject it

**Group:** ChatResponse

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production error response")
val resp = new_error_response("Connection failed")
expect(resp.content).to_equal("")
expect(resp.stop_reason).to_equal("error")
expect(resp.error).to_equal("Connection failed")
expect(resp.is_error).to_be(true)
expect(response_ok(resp)).to_be(false)
expect(response_has_content(resp)).to_be(false)
```

</details>

## should construct a successful response with content

**Group:** ChatResponse

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production successful response")
val resp = new_success_response("Hello!")
expect(resp.content).to_equal("Hello!")
expect(resp.stop_reason).to_equal("end_turn")
expect(resp.error).to_equal("")
expect(resp.is_error).to_be(false)
expect(response_ok(resp)).to_be(true)
expect(response_has_content(resp)).to_be(true)
```

</details>

## should treat empty successful content as absent

**Group:** ChatResponse

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production successful response without content")
val resp = new_success_response("")
expect(response_ok(resp)).to_be(true)
expect(response_has_content(resp)).to_be(false)
```

</details>

## should construct a generic event with empty metadata

**Group:** StreamEvent

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production generic stream event")
val evt: StreamEvent = new_stream_event("content_block_start", "payload")
expect(evt.event_type).to_equal("content_block_start")
expect(evt.content).to_equal("payload")
expect(evt.session_id).to_equal("")
expect(evt.model).to_equal("")
expect(evt.stop_reason).to_equal("")
expect(evt.input_tokens).to_equal(0)
expect(evt.output_tokens).to_equal(0)
```

</details>

## should construct a text delta

**Group:** StreamEvent

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production text-delta event")
val evt = new_text_delta("Hello ")
expect(evt.event_type).to_equal("text_delta")
expect(evt.content).to_equal("Hello ")
expect(evt.stop_reason).to_equal("")
```

</details>

## should construct a message-stop event

**Group:** StreamEvent

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production message-stop event")
val evt = new_message_stop("end_turn")
expect(evt.event_type).to_equal("message_stop")
expect(evt.content).to_equal("")
expect(evt.stop_reason).to_equal("end_turn")
```

</details>

## should construct every provider default

**Group:** ProviderConfig

<details>
<summary>Executable SSpec</summary>

```simple
step("Construct a production provider configuration")
val cfg: ProviderConfig = new_provider_config("claude_cli")
expect(cfg.provider_type).to_equal("claude_cli")
expect(cfg.base_url).to_equal("")
expect(cfg.api_key).to_equal("")
expect(cfg.model).to_equal("")
expect(cfg.cli_path).to_equal("")
expect(cfg.python_path).to_equal("")
expect(cfg.model_path).to_equal("")
expect(cfg.extra_args.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
| Executed scenarios | 0 |
