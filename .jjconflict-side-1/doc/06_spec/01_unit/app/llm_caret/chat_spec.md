# LLM Caret Chat Unit Spec

> Source-synchronized unit manual. The current self-hosted SSpec runner is
> blocked before trustworthy scenario execution, so this document records
> 24 active scenarios and 0 executed scenarios.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 24 | 24 | 0 | 0 | 0 |

**Executable source:** `test/01_unit/app/llm_caret/chat_spec.spl`

## should start empty

**Group:** production chat history

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
val length = chat_history_len()
val role = chat_last_role()
val content = chat_last_content()
_reset_chat_state()
expect(length).to_equal(0)
expect(role).to_equal("")
expect(content).to_equal("")
```

</details>

## should add a user message

**Group:** production chat history

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_user("Hello")
val length = chat_history_len()
val role = chat_get_role(0)
val content = chat_get_content(0)
_reset_chat_state()
expect(length).to_equal(1)
expect(role).to_equal("user")
expect(content).to_equal("Hello")
```

</details>

## should add an assistant message

**Group:** production chat history

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_assistant("Hi there!")
val length = chat_history_len()
val role = chat_get_role(0)
val content = chat_get_content(0)
_reset_chat_state()
expect(length).to_equal(1)
expect(role).to_equal("assistant")
expect(content).to_equal("Hi there!")
```

</details>

## should preserve custom roles through the generic message API

**Group:** production chat history

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_message("tool", "tool fixture")
val role = chat_get_role(0)
val content = chat_get_content(0)
_reset_chat_state()
expect(role).to_equal("tool")
expect(content).to_equal("tool fixture")
```

</details>

## should maintain conversation order

**Group:** production chat history

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_user("Hi")
chat_add_assistant("Hello!")
chat_add_user("How are you?")
val length = chat_history_len()
val first = chat_get_role(0)
val second = chat_get_role(1)
val third = chat_get_role(2)
_reset_chat_state()
expect(length).to_equal(3)
expect(first).to_equal("user")
expect(second).to_equal("assistant")
expect(third).to_equal("user")
```

</details>

## should clear populated history

**Group:** production chat history

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_user("test")
chat_clear()
val length = chat_history_len()
val content = chat_last_content()
_reset_chat_state()
expect(length).to_equal(0)
expect(content).to_equal("")
```

</details>

## should return empty text for every out-of-bounds lookup

**Group:** production chat history

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_user("only")
val negative_role = chat_get_role(-1)
val high_role = chat_get_role(99)
val negative_content = chat_get_content(-1)
val high_content = chat_get_content(99)
_reset_chat_state()
expect(negative_role).to_equal("")
expect(high_role).to_equal("")
expect(negative_content).to_equal("")
expect(high_content).to_equal("")
```

</details>

## should return the last role and content

**Group:** production chat history

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_user("First")
chat_add_assistant("Second")
val role = chat_last_role()
val content = chat_last_content()
_reset_chat_state()
expect(role).to_equal("assistant")
expect(content).to_equal("Second")
```

</details>

## should retain only the last requested messages

**Group:** production chat truncation

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_user("msg1")
chat_add_assistant("resp1")
chat_add_user("msg2")
chat_add_assistant("resp2")
chat_truncate(2)
val length = chat_history_len()
val first = chat_get_content(0)
val second = chat_get_content(1)
_reset_chat_state()
expect(length).to_equal(2)
expect(first).to_equal("msg2")
expect(second).to_equal("resp2")
```

</details>

## should leave history unchanged when the limit exceeds its length

**Group:** production chat truncation

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_user("msg1")
chat_truncate(10)
val length = chat_history_len()
val content = chat_get_content(0)
_reset_chat_state()
expect(length).to_equal(1)
expect(content).to_equal("msg1")
```

</details>

## should clear history when truncating to zero

**Group:** production chat truncation

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_user("msg1")
chat_add_assistant("resp1")
chat_truncate(0)
val length = chat_history_len()
_reset_chat_state()
expect(length).to_equal(0)
```

</details>

## should auto-truncate after exceeding maximum history

**Group:** production chat truncation

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_set_max_history(3)
chat_add_user("a")
chat_add_assistant("b")
chat_add_user("c")
chat_add_assistant("d")
val length = chat_history_len()
val first = chat_get_content(0)
val last = chat_last_content()
_reset_chat_state()
expect(length).to_equal(3)
expect(first).to_equal("b")
expect(last).to_equal("d")
```

</details>

## should set and read the system prompt

**Group:** production chat system prompt

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_set_system_prompt("Be helpful")
val prompt = chat_get_system_prompt()
_reset_chat_state()
expect(prompt).to_equal("Be helpful")
```

</details>

## should clear the system prompt

**Group:** production chat system prompt

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_set_system_prompt("temporary")
chat_set_system_prompt("")
val prompt = chat_get_system_prompt()
_reset_chat_state()
expect(prompt).to_equal("")
```

</details>

## should build an empty messages array

**Group:** production chat JSON

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
val json = chat_build_messages_json()
_reset_chat_state()
expect(json).to_equal("[]")
```

</details>

## should build ordered role and content objects

**Group:** production chat JSON

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_user("Hi")
chat_add_assistant("Hello!")
val json = chat_build_messages_json()
_reset_chat_state()
expect(json).to_equal(
    "[{\"role\":\"user\",\"content\":\"Hi\"}," +
    "{\"role\":\"assistant\",\"content\":\"Hello!\"}]"
)
```

</details>

## should escape quotes slashes and control characters

**Group:** production chat JSON

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_state()
chat_add_message("custom", "quote \" slash \\ line\nnext\ttab\r")
val json = chat_build_messages_json()
_reset_chat_state()
expect(json).to_contain("\"role\":\"custom\"")
expect(json).to_contain("quote \\\"")
expect(json).to_contain("slash \\\\")
expect(json).to_contain("line\\nnext\\ttab\\r")
```

</details>

## should derive success and error statuses

**Group:** production tool result presentation

<details>
<summary>Executable SSpec</summary>

```simple
val ok = new_tool_result("call-ok", "done")
val failed = new_tool_error("call-failed", "failed")
expect(tool_call_status(ok)).to_equal("ok")
expect(tool_call_status(failed)).to_equal("error")
```

</details>

## should redact secrets from summaries

**Group:** production tool result presentation

<details>
<summary>Executable SSpec</summary>

```simple
val secret = "sk-ant-api03-ABCDEFGHIJ1234"
val summary = tool_call_summary(
    new_tool_error("call-secret", "failed " + secret)
)
expect(summary).to_contain("failed")
expect(summary.contains(secret)).to_be(false)
```

</details>

## should cap summaries at two hundred visible characters

**Group:** production tool result presentation

<details>
<summary>Executable SSpec</summary>

```simple
var content = "xxxxxxxxxx"
while content.len() < 240:
    content = content + content
val summary = tool_call_summary(
    new_tool_result("call-long", content)
)
expect(summary.len()).to_equal(203)
expect(summary).to_end_with("...")
```

</details>

## should wrap redacted tool results as untrusted transcript input

**Group:** production tool result presentation

<details>
<summary>Executable SSpec</summary>

```simple
val secret = "sk-ant-api03-ABCDEFGHIJ1234"
val call = new_tool_call("call-1", "bash", "{}")
val message = _tool_result_message(
    call, new_tool_error("call-1", "failed " + secret)
)
expect(message).to_start_with(
    "[tool_result bash id=call-1 error]\n"
)
expect(message).to_contain(
    "BEGIN UNTRUSTED CONTENT (source: tool:bash)"
)
expect(message.contains(secret)).to_be(false)
```

</details>

## should finish a text-only response in one iteration

**Group:** production agent loop

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_test_seams()
val result = run_agent_loop(
    default_policy("build/tmp/llm_caret_chat_test"),
    [Message(role: "user", content: "fixture")],
    _text_responder,
    3
)
_reset_chat_test_seams()
expect(result.final_text).to_equal("final fixture")
expect(result.iterations).to_equal(1)
expect(result.stopped_reason).to_equal("end_turn")
expect(result.tool_calls_made).to_equal(0)
expect(result.final_transcript.len()).to_equal(2)
expect(result.final_transcript[1].role).to_equal("assistant")
```

</details>

## should gate an unknown tool and render its error before continuing

**Group:** production agent loop

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_test_seams()
val result = run_agent_loop_rendered(
    default_policy("build/tmp/llm_caret_chat_test"),
    [Message(role: "user", content: "fixture")],
    _tool_then_text_responder,
    3,
    _capture_tool
)
val render_calls = CHAT_TEST_RENDER_CALLS
val render_name = CHAT_TEST_RENDER_NAME
val render_status = CHAT_TEST_RENDER_STATUS
val render_summary = CHAT_TEST_RENDER_SUMMARY
_reset_chat_test_seams()
expect(result.final_text).to_equal("finished fixture")
expect(result.iterations).to_equal(2)
expect(result.stopped_reason).to_equal("end_turn")
expect(result.tool_calls_made).to_equal(1)
expect(result.final_transcript.len()).to_equal(4)
expect(result.final_transcript[1].role).to_equal("assistant")
expect(result.final_transcript[2].role).to_equal("user")
expect(result.final_transcript[2].content).to_contain("tool_result")
expect(result.final_transcript[3].role).to_equal("assistant")
expect(render_calls).to_equal(1)
expect(render_name).to_equal("unknown_fixture_tool")
expect(render_status).to_equal("error")
expect(render_summary).to_contain("unknown tool")
```

</details>

## should stop a repeated tool loop at the requested cap

**Group:** production agent loop

<details>
<summary>Executable SSpec</summary>

```simple
_reset_chat_test_seams()
val result = run_agent_loop_rendered(
    default_policy("build/tmp/llm_caret_chat_test"),
    [Message(role: "user", content: "fixture")],
    _always_tool_responder,
    2,
    _capture_tool
)
val render_calls = CHAT_TEST_RENDER_CALLS
_reset_chat_test_seams()
expect(result.final_text).to_equal("waiting fixture")
expect(result.iterations).to_equal(2)
expect(result.stopped_reason).to_equal("max_iterations")
expect(result.tool_calls_made).to_equal(2)
expect(result.final_transcript.len()).to_equal(5)
expect(render_calls).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
| Executed scenarios | 0 |
