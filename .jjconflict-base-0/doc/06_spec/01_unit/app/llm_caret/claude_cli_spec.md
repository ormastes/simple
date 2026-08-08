# LLM Caret Claude Cli Unit Spec

> Source-synchronized unit manual. The current self-hosted SSpec runner is
> blocked before trustworthy scenario execution, so this document records
> 80 active scenarios and 0 executed scenarios.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 80 | 80 | 0 | 0 | 0 |

**Executable source:** `test/01_unit/app/llm_caret/claude_cli_spec.spl`

## should include prompt with -p flag

**Group:** build_claude_args - minimal

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hello", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "-p")).to_be(true)
expect(args_get_flag_value(args, "-p")).to_equal("Hello")
```

</details>

## should default to json output format

**Group:** build_claude_args - minimal

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--output-format")).to_equal("json")
```

</details>

## should have no model flag when empty

**Group:** build_claude_args - minimal

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--model")).to_be(false)
```

</details>

## should have no system-prompt flag when empty

**Group:** build_claude_args - minimal

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--system-prompt")).to_be(false)
```

</details>

## should have no resume flag when empty

**Group:** build_claude_args - minimal

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--resume")).to_be(false)
```

</details>

## should include model flag

**Group:** build_claude_args - model

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "claude-opus-4-20250514", "", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--model")).to_equal("claude-opus-4-20250514")
```

</details>

## should support sonnet model

**Group:** build_claude_args - model

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "claude-sonnet-4-20250514", "", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--model")).to_equal("claude-sonnet-4-20250514")
```

</details>

## should include system prompt

**Group:** build_claude_args - system prompt

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "You are a pirate", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--system-prompt")).to_equal("You are a pirate")
```

</details>

## should include session resume

**Group:** build_claude_args - session

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "abc-123", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--resume")).to_equal("abc-123")
```

</details>

## should include max turns

**Group:** build_claude_args - max turns

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 5, 0, "", [], [], false)
expect(args_get_flag_value(args, "--max-turns")).to_equal("5")
```

</details>

## should omit max turns when zero

**Group:** build_claude_args - max turns

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--max-turns")).to_be(false)
```

</details>

## should omit the unsupported max tokens flag

**Group:** build_claude_args - max tokens

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 4096, "", [], [], false)
expect(args_contain(args, "--max-tokens")).to_be(false)
```

</details>

## should allow an older custom CLI to opt in explicitly

**Group:** build_claude_args - max tokens

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 4096, "", [], ["--max-tokens", "4096"], false)
expect(args_get_flag_value(args, "--max-tokens")).to_equal("4096")
```

</details>

## should use stream-json format

**Group:** build_claude_args - streaming

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "stream-json", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--output-format")).to_equal("stream-json")
```

</details>

## should enable verbose for a production stream

**Group:** build_claude_args - streaming

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_stream_args("Hi", "sonnet", "Be concise", "session-1", 2)
expect(args_get_flag_value(args, "--output-format")).to_equal("stream-json")
expect(args_contain(args, "--verbose")).to_be(true)
expect(args_get_flag_value(args, "--model")).to_equal("sonnet")
expect(args_get_flag_value(args, "--resume")).to_equal("session-1")
```

</details>

## should include json schema

**Group:** build_claude_args - json schema

<details>
<summary>Executable SSpec</summary>

```simple
val schema = LB() + Q() + "type" + Q() + ":" + Q() + "object" + Q() + RB()
val args = build_claude_args("Hi", "", "", "", "", 0, 0, schema, [], [], false)
expect(args_get_flag_value(args, "--json-schema")).to_equal(schema)
```

</details>

## should omit json schema when empty

**Group:** build_claude_args - json schema

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--json-schema")).to_be(false)
```

</details>

## should include single tool

**Group:** build_claude_args - tools

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", ["Read"], [], false)
expect(args_contain(args, "--allowedTools")).to_be(true)
expect(args_get_flag_value(args, "--allowedTools")).to_equal("Read")
```

</details>

## should include multiple tools

**Group:** build_claude_args - tools

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", ["Read", "Write", "Bash"], [], false)
var count = 0
for arg in args:
    if arg == "--allowedTools":
        count = count + 1
expect(count).to_equal(1)
expect(args_contain(args, "Read")).to_be(true)
expect(args_contain(args, "Write")).to_be(true)
expect(args_contain(args, "Bash")).to_be(true)
```

</details>

## should skip empty tool entries

**Group:** build_claude_args - tools

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", ["", "Read", ""], [], false)
expect(args_get_flag_value(args, "--allowedTools")).to_equal("Read")
expect(args_contain(args, "")).to_be(false)
```

</details>

## should omit the variadic flag when every tool entry is empty

**Group:** build_claude_args - tools

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", ["", ""], [], false)
expect(args_contain(args, "--allowedTools")).to_be(false)
```

</details>

## should have no tools when empty

**Group:** build_claude_args - tools

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--allowedTools")).to_be(false)
```

</details>

## should include verbose flag

**Group:** build_claude_args - verbose

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], true)
expect(args_contain(args, "--verbose")).to_be(true)
```

</details>

## should omit verbose when false

**Group:** build_claude_args - verbose

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--verbose")).to_be(false)
```

</details>

## should append extra args

**Group:** build_claude_args - extra args

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], ["--no-cache"], false)
expect(args_contain(args, "--no-cache")).to_be(true)
```

</details>

## should skip empty extra args

**Group:** build_claude_args - extra args

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], ["", "--flag", ""], false)
expect(args_contain(args, "--flag")).to_be(true)
expect(args_contain(args, "")).to_be(false)
```

</details>

## should build complete args

**Group:** build_claude_args - combined

<details>
<summary>Executable SSpec</summary>

```simple
val args = build_claude_args("prompt", "claude-opus-4-20250514", "json", "be helpful", "sess-1", 3, 2048, "", ["Read"], ["--no-cache"], true)
expect(args_get_flag_value(args, "-p")).to_equal("prompt")
expect(args_get_flag_value(args, "--model")).to_equal("claude-opus-4-20250514")
expect(args_get_flag_value(args, "--output-format")).to_equal("json")
expect(args_get_flag_value(args, "--system-prompt")).to_equal("be helpful")
expect(args_get_flag_value(args, "--resume")).to_equal("sess-1")
expect(args_get_flag_value(args, "--max-turns")).to_equal("3")
expect(args_contain(args, "--max-tokens")).to_be(false)
expect(args_contain(args, "--verbose")).to_be(true)
expect(args_contain(args, "--no-cache")).to_be(true)
```

</details>

## should parse successful response

**Group:** parse_claude_json_response - success

<details>
<summary>Executable SSpec</summary>

```simple
val json = mock_json("Hello world!", "claude-sonnet-4-20250514", "sess-abc")
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal("Hello world!")
expect(resp.model).to_equal("claude-sonnet-4-20250514")
expect(resp.session_id).to_equal("sess-abc")
expect(resp.is_error).to_be(false)
```

</details>

## should parse token counts

**Group:** parse_claude_json_response - success

<details>
<summary>Executable SSpec</summary>

```simple
val json = mock_json("Hi", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.input_tokens).to_equal(150)
expect(resp.output_tokens).to_equal(42)
```

</details>

## should parse stop reason

**Group:** parse_claude_json_response - success

<details>
<summary>Executable SSpec</summary>

```simple
val json = mock_json("Hi", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

## should preserve raw json

**Group:** parse_claude_json_response - success

<details>
<summary>Executable SSpec</summary>

```simple
val json = mock_json("Hi", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.raw).to_equal(json)
```

</details>

## should parse error response

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val json = mock_error_json("Rate limited")
val resp = parse_claude_json_response(json)
expect(resp.is_error).to_be(true)
expect(resp.error).to_equal("Rate limited")
expect(resp.content).to_equal("")
expect(resp.stop_reason).to_equal("error")
```

</details>

## should clear and redact secret-bearing error content

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val resp = parse_claude_json_response(
    "{\"result\":\"failed sk-ant-fixture-secret\",\"is_error\":true}"
)
expect(resp.is_error).to_be(true)
expect(resp.content).to_equal("")
expect(resp.error.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

## should handle empty response

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val resp = parse_claude_json_response("")
expect(resp.is_error).to_be(true)
expect(resp.error).to_equal("empty response")
```

</details>

## should handle whitespace-only response

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val resp = parse_claude_json_response("   ")
expect(resp.is_error).to_be(true)
expect(resp.error).to_equal("empty response")
```

</details>

## should reject malformed nonempty JSON

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val resp = parse_claude_json_response("not-json")
expect(resp.is_error).to_be(true)
expect(resp.stop_reason).to_equal("error")
expect(resp.error).to_equal("invalid JSON response from claude CLI")
```

</details>

## should reject an object without a result contract

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val resp = parse_claude_json_response("{}")
expect(resp.is_error).to_be(true)
expect(resp.error).to_equal("claude CLI response is missing result")
```

</details>

## should reject result and error fields with the wrong types

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val object_result = parse_claude_json_response(
    "{\"result\":{},\"is_error\":false}"
)
expect(object_result.is_error).to_be(true)
expect(object_result.error).to_contain("must be a string")
val text_error_flag = parse_claude_json_response(
    "{\"result\":\"x\",\"is_error\":\"true\"}"
)
expect(text_error_flag.is_error).to_be(true)
expect(text_error_flag.error).to_contain("must be boolean")
```

</details>

## should reject nonnumeric usage counters

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val resp = parse_claude_json_response(
    "{\"result\":\"x\",\"usage\":{\"input_tokens\":\"many\"}}"
)
expect(resp.is_error).to_be(true)
expect(resp.error).to_contain("must be numeric")
```

</details>

## should reject negative and fractional usage counters

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val negative = parse_claude_json_response(
    "{\"result\":\"x\",\"usage\":{\"input_tokens\":-1}}"
)
expect(negative.is_error).to_be(true)
expect(negative.error).to_contain("non-negative integers")
val fractional = parse_claude_json_response(
    "{\"result\":\"x\",\"message\":{\"usage\":{\"output_tokens\":1.5}}}"
)
expect(fractional.is_error).to_be(true)
expect(fractional.error).to_contain("non-negative integers")
```

</details>

## should reject malformed nested message usage and metadata

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val nested_usage = parse_claude_json_response(
    "{\"result\":\"x\",\"message\":{\"usage\":{\"output_tokens\":\"many\"}}}"
)
expect(nested_usage.is_error).to_be(true)
expect(nested_usage.error).to_contain("must be numeric")
val bad_model = parse_claude_json_response(
    "{\"result\":\"x\",\"model\":42}"
)
expect(bad_model.is_error).to_be(true)
expect(bad_model.error).to_contain("must be strings")
```

</details>

## should preserve an explicit zero counter over nested usage

**Group:** parse_claude_json_response - error

<details>
<summary>Executable SSpec</summary>

```simple
val resp = parse_claude_json_response(
    "{\"result\":\"x\",\"input_tokens\":0,\"usage\":{\"input_tokens\":9}}"
)
expect(resp.is_error).to_be(false)
expect(resp.input_tokens).to_equal(0)
```

</details>

## should handle missing model field

**Group:** parse_claude_json_response - edge cases

<details>
<summary>Executable SSpec</summary>

```simple
var json = LB()
json = json + Q() + "result" + Q() + ":" + Q() + "Hello" + Q() + ","
json = json + Q() + "is_error" + Q() + ":false"
json = json + RB()
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal("Hello")
expect(resp.model).to_equal("")
```

</details>

## should default stop reason to end_turn

**Group:** parse_claude_json_response - edge cases

<details>
<summary>Executable SSpec</summary>

```simple
var json = LB()
json = json + Q() + "result" + Q() + ":" + Q() + "Done" + Q() + ","
json = json + Q() + "is_error" + Q() + ":false"
json = json + RB()
val resp = parse_claude_json_response(json)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

## should handle multiline result content

**Group:** parse_claude_json_response - edge cases

<details>
<summary>Executable SSpec</summary>

```simple
val expected = "Line 1\nLine 2"
val json = mock_json(expected, "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal(expected)
```

</details>

## should unescape quotes and backslashes in result content

**Group:** parse_claude_json_response - edge cases

<details>
<summary>Executable SSpec</summary>

```simple
val expected = "Use \"quoted\" text and C:\\workspace"
val json = mock_json(expected, "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal(expected)
```

</details>

## should preserve structured output when result text is absent

**Group:** parse_claude_json_response - edge cases

<details>
<summary>Executable SSpec</summary>

```simple
val json = "{\"type\":\"result\",\"structured_output\":{\"name\":\"Simple\",\"items\":[1,2],\"note\":\"brace } text\"},\"session_id\":\"sess\",\"is_error\":false}"
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal(
    "{\"name\":\"Simple\",\"items\":[1,2],\"note\":\"brace } text\"}"
)
```

</details>

## should accept legal whitespace around object separators

**Group:** parse_claude_json_response - edge cases

<details>
<summary>Executable SSpec</summary>

```simple
val json = "{ \"result\" : \"spaced\", \"is_error\" : false }"
val resp = parse_claude_json_response(json)
expect(resp.is_error).to_be(false)
expect(resp.content).to_equal("spaced")
```

</details>

## should preserve scalar structured output as JSON

**Group:** parse_claude_json_response - edge cases

<details>
<summary>Executable SSpec</summary>

```simple
val text_value = parse_claude_json_response(
    "{\"structured_output\":\"answer\",\"is_error\":false}"
)
expect(text_value.content).to_equal("\"answer\"")
val null_value = parse_claude_json_response(
    "{\"structured_output\":null,\"is_error\":false}"
)
expect(null_value.content).to_equal("null")
```

</details>

## should parse content_block_delta

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = mock_stream_line("content_block_delta", "Hello ")
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("content_block_delta")
expect(evt.content).to_equal("Hello ")
```

</details>

## should unescape streamed text deltas

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val expected = "first\nsecond"
val line = mock_stream_line("content_block_delta", expected)
val evt = parse_claude_stream_line(line)
expect(evt.content).to_equal(expected)
```

</details>

## should parse message_stop

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
var line = LB()
line = line + Q() + "type" + Q() + ":" + Q() + "message_stop" + Q() + ","
line = line + Q() + "stop_reason" + Q() + ":" + Q() + "end_turn" + Q()
line = line + RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("message_stop")
expect(evt.stop_reason).to_equal("end_turn")
```

</details>

## should parse message_start with model

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
var line = LB()
line = line + Q() + "type" + Q() + ":" + Q() + "message_start" + Q() + ","
line = line + Q() + "message" + Q() + ":{"
line = line + Q() + "model" + Q() + ":" + Q() + "claude-sonnet-4-20250514" + Q() + ","
line = line + Q() + "usage" + Q() + ":{"
line = line + Q() + "input_tokens" + Q() + ":25,"
line = line + Q() + "output_tokens" + Q() + ":1}}"
line = line + RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("message_start")
expect(evt.model).to_equal("claude-sonnet-4-20250514")
expect(evt.input_tokens).to_equal(25)
expect(evt.output_tokens).to_equal(1)
```

</details>

## should parse message_delta usage and stop reason

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"message_delta\",\"delta\":{\"stop_reason\":\"end_turn\"},\"usage\":{\"output_tokens\":15}}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("message_delta")
expect(evt.stop_reason).to_equal("end_turn")
expect(evt.output_tokens).to_equal(15)
```

</details>

## should parse a Claude Code system init envelope

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"system\",\"subtype\":\"init\",\"session_id\":\"session-init\",\"model\":\"claude-sonnet-4-6\"}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("system")
expect(evt.session_id).to_equal("session-init")
expect(evt.model).to_equal("claude-sonnet-4-6")
```

</details>

## should parse a Claude Code assistant envelope

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"assistant\",\"message\":{\"model\":\"claude-sonnet-4-6\",\"content\":[{\"type\":\"text\",\"text\":\"Hello from Claude\"}],\"usage\":{\"input_tokens\":12,\"output_tokens\":4}},\"session_id\":\"session-a\"}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("assistant")
expect(evt.content).to_equal("Hello from Claude")
expect(evt.session_id).to_equal("session-a")
expect(evt.input_tokens).to_equal(12)
expect(evt.output_tokens).to_equal(4)
```

</details>

## should aggregate every assistant text block

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"text\",\"text\":\"one\"},{\"type\":\"tool_use\",\"name\":\"Read\"},{\"type\":\"text\",\"text\":\" two\"}]}}"
val evt = parse_claude_stream_line(line)
expect(evt.content).to_equal("one two")
```

</details>

## should parse a Claude Code result envelope

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"result\",\"subtype\":\"success\",\"is_error\":false,\"result\":\"done\",\"session_id\":\"session-r\",\"stop_reason\":\"end_turn\",\"usage\":{\"input_tokens\":20,\"output_tokens\":6}}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("result")
expect(evt.content).to_equal("done")
expect(evt.session_id).to_equal("session-r")
expect(evt.stop_reason).to_equal("end_turn")
expect(evt.input_tokens).to_equal(20)
expect(evt.output_tokens).to_equal(6)
```

</details>

## should reject malformed stream result contracts

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val bad_flag = parse_claude_stream_line(
    "{\"type\":\"result\",\"is_error\":\"false\",\"result\":\"done\"}"
)
expect(bad_flag.stop_reason).to_equal("invalid")
expect(bad_flag.content).to_contain("must be boolean")
val bad_result = parse_claude_stream_line(
    "{\"type\":\"result\",\"is_error\":false,\"result\":42}"
)
expect(bad_result.stop_reason).to_equal("invalid")
expect(bad_result.content).to_contain("must be a string")
```

</details>

## should default message stop and reject malformed stream metadata

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val stopped = parse_claude_stream_line(
    "{\"type\":\"message_stop\"}"
)
expect(stopped.stop_reason).to_equal("end_turn")
val root_model = parse_claude_stream_line(
    "{\"type\":\"system\",\"model\":42}"
)
expect(root_model.stop_reason).to_equal("invalid")
expect(root_model.content).to_contain("metadata fields")
val nested_model = parse_claude_stream_line(
    "{\"type\":\"assistant\",\"message\":{\"model\":42,\"content\":[]}}"
)
expect(nested_model.stop_reason).to_equal("invalid")
expect(nested_model.content).to_contain("message model")
```

</details>

## should reject malformed assistant content and usage values

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val scalar_content = parse_claude_stream_line(
    "{\"type\":\"assistant\",\"message\":{\"content\":\"text\"}}"
)
expect(scalar_content.stop_reason).to_equal("invalid")
expect(scalar_content.content).to_contain("must be an array")
val bad_block = parse_claude_stream_line(
    "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"text\",\"text\":42}]}}"
)
expect(bad_block.stop_reason).to_equal("invalid")
expect(bad_block.content).to_contain("typed objects")
val fractional_usage = parse_claude_stream_line(
    "{\"type\":\"result\",\"is_error\":false,\"result\":\"done\",\"usage\":{\"output_tokens\":2.5}}"
)
expect(fractional_usage.stop_reason).to_equal("invalid")
expect(fractional_usage.content).to_contain("non-negative integers")
```

</details>

## should parse structured output from a Claude Code result envelope

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"result\",\"subtype\":\"success\",\"is_error\":false,\"structured_output\":{\"answer\":42,\"labels\":[\"a\",\"b\"]},\"session_id\":\"session-r\"}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("result")
expect(evt.content).to_equal(
    "{\"answer\":42,\"labels\":[\"a\",\"b\"]}"
)
```

</details>

## should parse a streaming error envelope

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"error\",\"error\":{\"type\":\"overloaded_error\",\"message\":\"Overloaded\"}}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("error")
expect(evt.content).to_equal("Overloaded")
expect(evt.stop_reason).to_equal("error")
```

</details>

## should redact secrets in streaming protocol errors

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"error\",\"error\":{\"message\":\"failed sk-ant-fixture-secret\"}}"
val evt = parse_claude_stream_line(line)
expect(evt.content.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

## should redact secrets in error result envelopes

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"result\",\"is_error\":true,\"result\":\"failed sk-ant-fixture-secret\"}"
val evt = parse_claude_stream_line(line)
expect(evt.content.contains("sk-ant-fixture-secret")).to_be(false)
expect(evt.stop_reason).to_equal("error")
```

</details>

## should preserve a nested diagnostic from an error-only result

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"result\",\"is_error\":true,\"error\":{\"message\":\"provider overloaded\"}}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("result")
expect(evt.content).to_equal("provider overloaded")
expect(evt.stop_reason).to_equal("error")
```

</details>

## should accept a string protocol error and redact it

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val line = "{\"type\":\"error\",\"error\":\"failed sk-ant-fixture-secret\"}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("error")
expect(evt.content).to_contain("[REDACTED:")
expect(evt.content.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

## should reject malformed nested stream fields

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val nested_usage = parse_claude_stream_line(
    "{\"type\":\"assistant\",\"message\":{\"usage\":{\"input_tokens\":\"many\"}}}"
)
expect(nested_usage.stop_reason).to_equal("invalid")
expect(nested_usage.content).to_contain("must be numeric")
val scalar_delta = parse_claude_stream_line(
    "{\"type\":\"content_block_delta\",\"delta\":\"text\"}"
)
expect(scalar_delta.stop_reason).to_equal("invalid")
expect(scalar_delta.content).to_contain("must be an object")
```

</details>

## should preserve explicit zero stream usage and partial JSON

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val started = parse_claude_stream_line(
    "{\"type\":\"message_start\",\"input_tokens\":0,\"message\":{\"usage\":{\"input_tokens\":9}}}"
)
expect(started.input_tokens).to_equal(0)
val delta = parse_claude_stream_line(
    "{\"type\":\"content_block_delta\",\"delta\":{\"partial_json\":\"{\\\"x\\\":\"}}"
)
expect(delta.content).to_equal("{\"x\":")
```

</details>

## should accept non-content protocol events without forging terminal state

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
for event_type in ["content_block_start", "content_block_stop", "ping", "user", "rate_limit_event"]:
    val evt = parse_claude_stream_line(
        "{\"type\":\"" + event_type + "\"}"
    )
    expect(evt.event_type).to_equal(event_type)
    expect(evt.stop_reason).to_equal("")
```

</details>

## should handle empty line

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val evt = parse_claude_stream_line("")
expect(evt.event_type).to_equal("empty")
```

</details>

## should reject an event without a type

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
var line = LB()
line = line + Q() + "data" + Q() + ":" + Q() + "something" + Q()
line = line + RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("error")
expect(evt.stop_reason).to_equal("invalid")
```

</details>

## should reject malformed stream JSON

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val evt = parse_claude_stream_line("not-json")
expect(evt.event_type).to_equal("error")
expect(evt.stop_reason).to_equal("invalid")
```

</details>

## should reject unsupported typed stream events

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val evt = parse_claude_stream_line(
    "{\"type\":\"forged_terminal\",\"result\":\"done\"}"
)
expect(evt.event_type).to_equal("error")
expect(evt.stop_reason).to_equal("invalid")
expect(evt.content).to_contain("unsupported")
```

</details>

## should reject a contract-free result event

**Group:** parse_claude_stream_line

<details>
<summary>Executable SSpec</summary>

```simple
val evt = parse_claude_stream_line("{\"type\":\"result\"}")
expect(evt.event_type).to_equal("error")
expect(evt.stop_reason).to_equal("invalid")
expect(evt.content).to_contain("missing result")
```

</details>

## should forward advanced arguments and preserve response metadata

**Group:** claude_cli_send - local fixture

<details>
<summary>Executable SSpec</summary>

```simple
val resp = claude_cli_send(
    MOCK_CLAUDE_CLI, "fixture-advanced", "sonnet", "", "", 0, 0,
    "{\"type\":\"object\"}", ["Read"], ["--fixture-extra"]
)
expect(resp.is_error).to_be(false)
expect(resp.content).to_equal("advanced-ok")
expect(resp.model).to_equal("sonnet")
expect(resp.session_id).to_equal("advanced-session")
```

</details>

## should fail closed and redact subprocess diagnostics

**Group:** claude_cli_send - local fixture

<details>
<summary>Executable SSpec</summary>

```simple
val malformed = claude_cli_send(
    MOCK_CLAUDE_CLI, "fixture-json-malformed", "sonnet",
    "", "", 0, 0, "", [], []
)
expect(malformed.is_error).to_be(true)
expect(malformed.error).to_contain("invalid JSON")

val failed = claude_cli_send(
    MOCK_CLAUDE_CLI, "fixture-error", "sonnet",
    "", "", 0, 0, "", [], []
)
expect(failed.is_error).to_be(true)
expect(failed.stop_reason).to_equal("error")
expect(failed.error).to_contain("[REDACTED:")
expect(failed.error.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

## should return a complete ordered stream

**Group:** claude_cli_stream - local fixture

<details>
<summary>Executable SSpec</summary>

```simple
val events = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream", "sonnet",
    "Be concise", "", 1
)
expect(events.len()).to_equal(3)
expect(events[0].event_type).to_equal("system")
expect(events[0].session_id).to_equal("stream-session")
expect(events[1].event_type).to_equal("assistant")
expect(events[1].content).to_equal("streamed fixture")
expect(events[2].event_type).to_equal("result")
expect(events[2].content).to_equal("stream complete")
expect(events[2].output_tokens).to_equal(3)
```

</details>

## should reject malformed and duplicate terminal streams

**Group:** claude_cli_stream - local fixture

<details>
<summary>Executable SSpec</summary>

```simple
val malformed = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-malformed-then-result",
    "sonnet", "", "", 1
)
expect(malformed.len()).to_equal(1)
expect(malformed[0].stop_reason).to_equal("invalid")
expect(malformed[0].content).to_contain("invalid JSON")

val duplicate = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-duplicate-terminal",
    "sonnet", "", "", 1
)
expect(duplicate.len()).to_equal(1)
expect(duplicate[0].stop_reason).to_equal("invalid")
expect(duplicate[0].content).to_contain("after a terminal")
```

</details>

## should distinguish incomplete, empty, and valid stop-result streams

**Group:** claude_cli_stream - local fixture

<details>
<summary>Executable SSpec</summary>

```simple
val incomplete = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-incomplete",
    "sonnet", "", "", 1
)
expect(incomplete.len()).to_equal(2)
expect(incomplete[1].event_type).to_equal("error")
expect(incomplete[1].content).to_contain("before a terminal event")

val empty = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-empty", "sonnet", "", "", 1
)
expect(empty.len()).to_equal(1)
expect(empty[0].content).to_contain("no valid stream events")

val completed = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-stop-then-result",
    "sonnet", "", "", 1
)
expect(completed.len()).to_equal(2)
expect(completed[0].event_type).to_equal("message_stop")
expect(completed[1].event_type).to_equal("result")
expect(completed[1].content).to_equal("complete")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 80 |
| Active scenarios | 80 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
| Executed scenarios | 0 |
