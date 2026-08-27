# claude_cli_spec

> Purpose: Prove that build_claude_args - minimal.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 84 | 84 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# claude_cli_spec

Purpose: Prove that build_claude_args - minimal.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that build_claude_args - minimal.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### build_claude_args - minimal

#### should include prompt with -p flag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should include prompt with -p flag
- Verify: should include prompt with -p flag
   - Expected: args_get_flag_value(args, "-p") equals `Hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should include prompt with -p flag")
step("Verify: should include prompt with -p flag")
# @req: REQ-APP-LLM-CARET-001
val args = build_claude_args("Hello", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "-p")).to_be(true)
expect(args_get_flag_value(args, "-p")).to_equal("Hello")
```

</details>

#### should default to json output format

- should default to json output format
- Verify: should default to json output format
   - Expected: args_get_flag_value(args, "--output-format") equals `json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should default to json output format")
step("Verify: should default to json output format")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--output-format")).to_equal("json")
```

</details>

#### should have no model flag when empty

- should have no model flag when empty
- Verify: should have no model flag when empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should have no model flag when empty")
step("Verify: should have no model flag when empty")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--model")).to_be(false)
```

</details>

#### should have no system-prompt flag when empty

- should have no system-prompt flag when empty
- Verify: should have no system-prompt flag when empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should have no system-prompt flag when empty")
step("Verify: should have no system-prompt flag when empty")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--system-prompt")).to_be(false)
```

</details>

#### should have no resume flag when empty

- should have no resume flag when empty
- Verify: should have no resume flag when empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should have no resume flag when empty")
step("Verify: should have no resume flag when empty")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--resume")).to_be(false)
```

</details>

### build_claude_args - model

#### should include model flag

- should include model flag
- Verify: should include model flag
   - Expected: args_get_flag_value(args, "--model") equals `claude-opus-4-20250514`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should include model flag")
step("Verify: should include model flag")
val args = build_claude_args("Hi", "claude-opus-4-20250514", "", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--model")).to_equal("claude-opus-4-20250514")
```

</details>

#### should support sonnet model

- should support sonnet model
- Verify: should support sonnet model
   - Expected: args_get_flag_value(args, "--model") equals `claude-sonnet-4-20250514`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should support sonnet model")
step("Verify: should support sonnet model")
val args = build_claude_args("Hi", "claude-sonnet-4-20250514", "", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--model")).to_equal("claude-sonnet-4-20250514")
```

</details>

### build_claude_args - system prompt

#### should include system prompt

- should include system prompt
- Verify: should include system prompt
   - Expected: args_get_flag_value(args, "--system-prompt") equals `You are a pirate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should include system prompt")
step("Verify: should include system prompt")
val args = build_claude_args("Hi", "", "", "You are a pirate", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--system-prompt")).to_equal("You are a pirate")
```

</details>

### build_claude_args - session

#### should include session resume

- should include session resume
- Verify: should include session resume
   - Expected: args_get_flag_value(args, "--resume") equals `abc-123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should include session resume")
step("Verify: should include session resume")
val args = build_claude_args("Hi", "", "", "", "abc-123", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--resume")).to_equal("abc-123")
```

</details>

### build_claude_args - max turns

#### should include max turns

- should include max turns
- Verify: should include max turns
   - Expected: args_get_flag_value(args, "--max-turns") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should include max turns")
step("Verify: should include max turns")
val args = build_claude_args("Hi", "", "", "", "", 5, 0, "", [], [], false)
expect(args_get_flag_value(args, "--max-turns")).to_equal("5")
```

</details>

#### should omit max turns when zero

- should omit max turns when zero
- Verify: should omit max turns when zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should omit max turns when zero")
step("Verify: should omit max turns when zero")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--max-turns")).to_be(false)
```

</details>

### build_claude_args - max tokens

#### should omit the unsupported max tokens flag

- should omit the unsupported max tokens flag
- Verify: should omit the unsupported max tokens flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should omit the unsupported max tokens flag")
step("Verify: should omit the unsupported max tokens flag")
val args = build_claude_args("Hi", "", "", "", "", 0, 4096, "", [], [], false)
expect(args_contain(args, "--max-tokens")).to_be(false)
```

</details>

#### should allow an older custom CLI to opt in explicitly

- should allow an older custom CLI to opt in explicitly
- Verify: should allow an older custom CLI to opt in explicitly
   - Expected: args_get_flag_value(args, "--max-tokens") equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should allow an older custom CLI to opt in explicitly")
step("Verify: should allow an older custom CLI to opt in explicitly")
val args = build_claude_args("Hi", "", "", "", "", 0, 4096, "", [], ["--max-tokens", "4096"], false)
expect(args_get_flag_value(args, "--max-tokens")).to_equal("4096")
```

</details>

### build_claude_args - streaming

#### should use stream-json format

- should use stream-json format
- Verify: should use stream-json format
   - Expected: args_get_flag_value(args, "--output-format") equals `stream-json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should use stream-json format")
step("Verify: should use stream-json format")
val args = build_claude_args("Hi", "", "stream-json", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--output-format")).to_equal("stream-json")
```

</details>

#### should enable verbose for a production stream

- should enable verbose for a production stream
- Verify: should enable verbose for a production stream
   - Expected: args_get_flag_value(args, "--output-format") equals `stream-json`
   - Expected: args_get_flag_value(args, "--model") equals `sonnet`
   - Expected: args_get_flag_value(args, "--resume") equals `session-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should enable verbose for a production stream")
step("Verify: should enable verbose for a production stream")
val args = build_claude_stream_args("Hi", "sonnet", "Be concise", "session-1", 2)
expect(args_get_flag_value(args, "--output-format")).to_equal("stream-json")
expect(args_contain(args, "--verbose")).to_be(true)
expect(args_get_flag_value(args, "--model")).to_equal("sonnet")
expect(args_get_flag_value(args, "--resume")).to_equal("session-1")
```

</details>

### build_claude_args - json schema

#### should include json schema

- should include json schema
- Verify: should include json schema
   - Expected: args_get_flag_value(args, "--json-schema") equals `schema`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should include json schema")
step("Verify: should include json schema")
val schema = LB() + Q() + "type" + Q() + ":" + Q() + "object" + Q() + RB()
val args = build_claude_args("Hi", "", "", "", "", 0, 0, schema, [], [], false)
expect(args_get_flag_value(args, "--json-schema")).to_equal(schema)
```

</details>

#### should omit json schema when empty

- should omit json schema when empty
- Verify: should omit json schema when empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should omit json schema when empty")
step("Verify: should omit json schema when empty")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--json-schema")).to_be(false)
```

</details>

### build_claude_args - tools

#### should include single tool

- should include single tool
- Verify: should include single tool
   - Expected: args_get_flag_value(args, "--allowedTools") equals `Read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should include single tool")
step("Verify: should include single tool")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", ["Read"], [], false)
expect(args_contain(args, "--allowedTools")).to_be(true)
expect(args_get_flag_value(args, "--allowedTools")).to_equal("Read")
```

</details>

#### should include multiple tools

- should include multiple tools
- Verify: should include multiple tools
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should include multiple tools")
step("Verify: should include multiple tools")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", ["Read", "Write", "Bash"], [], false)
var count = 0
for arg in args:
    if arg == "--allowedTools":
        count = count + 1
expect(count).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(args_contain(args, "Read")).to_be(true)
expect(args_contain(args, "Write")).to_be(true)
expect(args_contain(args, "Bash")).to_be(true)
```

</details>

#### should skip empty tool entries

- should skip empty tool entries
- Verify: should skip empty tool entries
   - Expected: args_get_flag_value(args, "--allowedTools") equals `Read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should skip empty tool entries")
step("Verify: should skip empty tool entries")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", ["", "Read", ""], [], false)
expect(args_get_flag_value(args, "--allowedTools")).to_equal("Read")
expect(args_contain(args, "")).to_be(false)
```

</details>

#### should omit the variadic flag when every tool entry is empty

- should omit the variadic flag when every tool entry is empty
- Verify: should omit the variadic flag when every tool entry is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should omit the variadic flag when every tool entry is empty")
step("Verify: should omit the variadic flag when every tool entry is empty")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", ["", ""], [], false)
expect(args_contain(args, "--allowedTools")).to_be(false)
```

</details>

#### should have no tools when empty

- should have no tools when empty
- Verify: should have no tools when empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should have no tools when empty")
step("Verify: should have no tools when empty")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--allowedTools")).to_be(false)
```

</details>

### build_claude_args - verbose

#### should include verbose flag

- should include verbose flag
- Verify: should include verbose flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should include verbose flag")
step("Verify: should include verbose flag")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], true)
expect(args_contain(args, "--verbose")).to_be(true)
```

</details>

#### should omit verbose when false

- should omit verbose when false
- Verify: should omit verbose when false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should omit verbose when false")
step("Verify: should omit verbose when false")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--verbose")).to_be(false)
```

</details>

### build_claude_args - extra args

#### should append extra args

- should append extra args
- Verify: should append extra args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should append extra args")
step("Verify: should append extra args")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], ["--no-cache"], false)
expect(args_contain(args, "--no-cache")).to_be(true)
```

</details>

#### should skip empty extra args

- should skip empty extra args
- Verify: should skip empty extra args


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should skip empty extra args")
step("Verify: should skip empty extra args")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], ["", "--flag", ""], false)
expect(args_contain(args, "--flag")).to_be(true)
expect(args_contain(args, "")).to_be(false)
```

</details>

### build_claude_args - combined

#### should build complete args

- should build complete args
- Verify: should build complete args
   - Expected: args_get_flag_value(args, "-p") equals `prompt`
   - Expected: args_get_flag_value(args, "--model") equals `claude-opus-4-20250514`
   - Expected: args_get_flag_value(args, "--output-format") equals `json`
   - Expected: args_get_flag_value(args, "--system-prompt") equals `be helpful`
   - Expected: args_get_flag_value(args, "--resume") equals `sess-1`
   - Expected: args_get_flag_value(args, "--max-turns") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should build complete args")
step("Verify: should build complete args")
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

### parse_claude_json_response - success

#### should parse successful response

- should parse successful response
- Verify: should parse successful response
   - Expected: resp.content equals `Hello world!`
   - Expected: resp.model equals `claude-sonnet-4-20250514`
   - Expected: resp.session_id equals `sess-abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse successful response")
step("Verify: should parse successful response")
val json = mock_json("Hello world!", "claude-sonnet-4-20250514", "sess-abc")
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal("Hello world!")
expect(resp.model).to_equal("claude-sonnet-4-20250514")
expect(resp.session_id).to_equal("sess-abc")
expect(resp.is_error).to_be(false)
```

</details>

#### should parse token counts

- should parse token counts
- Verify: should parse token counts
   - Expected: resp.input_tokens equals `150`
   - Expected: resp.output_tokens equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse token counts")
step("Verify: should parse token counts")
val json = mock_json("Hi", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.input_tokens).to_equal(150)  # oracle: 150 — named expected value from the requirement
expect(resp.output_tokens).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### should parse stop reason

- should parse stop reason
- Verify: should parse stop reason
   - Expected: resp.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse stop reason")
step("Verify: should parse stop reason")
val json = mock_json("Hi", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

#### should preserve raw json

- should preserve raw json
- Verify: should preserve raw json
   - Expected: resp.raw equals `json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should preserve raw json")
step("Verify: should preserve raw json")
val json = mock_json("Hi", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.raw).to_equal(json)
```

</details>

### parse_claude_json_response - error

#### should parse error response

- should parse error response
- Verify: should parse error response
   - Expected: resp.error equals `Rate limited`
   - Expected: resp.content equals ``
   - Expected: resp.stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse error response")
step("Verify: should parse error response")
val json = mock_error_json("Rate limited")
val resp = parse_claude_json_response(json)
expect(resp.is_error).to_be(true)
expect(resp.error).to_equal("Rate limited")
expect(resp.content).to_equal("")
expect(resp.stop_reason).to_equal("error")
```

</details>

#### should clear and redact secret-bearing error content

- should clear and redact secret-bearing error content
- Verify: should clear and redact secret-bearing error content
   - Expected: resp.content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should clear and redact secret-bearing error content")
step("Verify: should clear and redact secret-bearing error content")
val resp = parse_claude_json_response(
    "{\"result\":\"failed sk-ant-fixture-secret\",\"is_error\":true}"
)
expect(resp.is_error).to_be(true)
expect(resp.content).to_equal("")
expect(resp.error.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

#### should handle empty response

- should handle empty response
- Verify: should handle empty response
   - Expected: resp.error equals `empty response`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should handle empty response")
step("Verify: should handle empty response")
val resp = parse_claude_json_response("")
expect(resp.is_error).to_be(true)
expect(resp.error).to_equal("empty response")
```

</details>

#### should handle whitespace-only response

- should handle whitespace-only response
- Verify: should handle whitespace-only response
   - Expected: resp.error equals `empty response`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should handle whitespace-only response")
step("Verify: should handle whitespace-only response")
val resp = parse_claude_json_response("   ")
expect(resp.is_error).to_be(true)
expect(resp.error).to_equal("empty response")
```

</details>

#### should reject malformed nonempty JSON

- should reject malformed nonempty JSON
- Verify: should reject malformed nonempty JSON
   - Expected: resp.stop_reason equals `error`
   - Expected: resp.error equals `invalid JSON response from claude CLI`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject malformed nonempty JSON")
step("Verify: should reject malformed nonempty JSON")
val resp = parse_claude_json_response("not-json")
expect(resp.is_error).to_be(true)
expect(resp.stop_reason).to_equal("error")
expect(resp.error).to_equal("invalid JSON response from claude CLI")
```

</details>

#### should reject an object without a result contract

- should reject an object without a result contract
- Verify: should reject an object without a result contract
   - Expected: resp.error equals `claude CLI response is missing result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject an object without a result contract")
step("Verify: should reject an object without a result contract")
val resp = parse_claude_json_response("{}")
expect(resp.is_error).to_be(true)
expect(resp.error).to_equal("claude CLI response is missing result")
```

</details>

#### should reject result and error fields with the wrong types

- should reject result and error fields with the wrong types
- Verify: should reject result and error fields with the wrong types


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject result and error fields with the wrong types")
step("Verify: should reject result and error fields with the wrong types")
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

#### should reject nonnumeric usage counters

- should reject nonnumeric usage counters
- Verify: should reject nonnumeric usage counters


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject nonnumeric usage counters")
step("Verify: should reject nonnumeric usage counters")
val resp = parse_claude_json_response(
    "{\"result\":\"x\",\"usage\":{\"input_tokens\":\"many\"}" + RB()
)
expect(resp.is_error).to_be(true)
expect(resp.error).to_contain("must be numeric")
```

</details>

#### should reject negative and fractional usage counters

- should reject negative and fractional usage counters
- Verify: should reject negative and fractional usage counters


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject negative and fractional usage counters")
step("Verify: should reject negative and fractional usage counters")
val negative = parse_claude_json_response(
    "{\"result\":\"x\",\"usage\":{\"input_tokens\":-1}" + RB()
)
expect(negative.is_error).to_be(true)
expect(negative.error).to_contain("non-negative integers")
val fractional = parse_claude_json_response(
    "{\"result\":\"x\",\"message\":{\"usage\":{\"output_tokens\":1.5}" + RB() + RB()
)
expect(fractional.is_error).to_be(true)
expect(fractional.error).to_contain("non-negative integers")
```

</details>

#### should reject malformed nested message usage and metadata

- should reject malformed nested message usage and metadata
- Verify: should reject malformed nested message usage and metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject malformed nested message usage and metadata")
step("Verify: should reject malformed nested message usage and metadata")
val nested_usage = parse_claude_json_response(
    "{\"result\":\"x\",\"message\":{\"usage\":{\"output_tokens\":\"many\"}" + RB() + RB()
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

#### should preserve an explicit zero counter over nested usage

- should preserve an explicit zero counter over nested usage
- Verify: should preserve an explicit zero counter over nested usage
   - Expected: resp.input_tokens equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should preserve an explicit zero counter over nested usage")
step("Verify: should preserve an explicit zero counter over nested usage")
val resp = parse_claude_json_response(
    "{\"result\":\"x\",\"input_tokens\":0,\"usage\":{\"input_tokens\":9}" + RB()
)
expect(resp.is_error).to_be(false)
expect(resp.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### parse_claude_json_response - edge cases

#### should handle missing model field

- should handle missing model field
- Verify: should handle missing model field
   - Expected: resp.content equals `Hello`
   - Expected: resp.model equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should handle missing model field")
step("Verify: should handle missing model field")
var json = LB()
json = json + Q() + "result" + Q() + ":" + Q() + "Hello" + Q() + ","
json = json + Q() + "is_error" + Q() + ":false"
json = json + RB()
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal("Hello")
expect(resp.model).to_equal("")
```

</details>

#### should default stop reason to end_turn

- should default stop reason to end_turn
- Verify: should default stop reason to end_turn
   - Expected: resp.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should default stop reason to end_turn")
step("Verify: should default stop reason to end_turn")
var json = LB()
json = json + Q() + "result" + Q() + ":" + Q() + "Done" + Q() + ","
json = json + Q() + "is_error" + Q() + ":false"
json = json + RB()
val resp = parse_claude_json_response(json)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

#### should handle multiline result content

- should handle multiline result content
- Verify: should handle multiline result content
   - Expected: resp.content equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should handle multiline result content")
step("Verify: should handle multiline result content")
val expected = "Line 1\nLine 2"
val json = mock_json(expected, "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal(expected)
```

</details>

#### should unescape quotes and backslashes in result content

- should unescape quotes and backslashes in result content
- Verify: should unescape quotes and backslashes in result content
   - Expected: resp.content equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should unescape quotes and backslashes in result content")
step("Verify: should unescape quotes and backslashes in result content")
val expected = "Use \"quoted\" text and C:\\workspace"
val json = mock_json(expected, "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal(expected)
```

</details>

#### should preserve structured output when result text is absent

- should preserve structured output when result text is absent
- Verify: should preserve structured output when result text is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should preserve structured output when result text is absent")
step("Verify: should preserve structured output when result text is absent")
val json = "{\"type\":\"result\",\"structured_output\":{\"name\":\"Simple\",\"items\":[1,2],\"note\":\"brace } text\"},\"session_id\":\"sess\",\"is_error\":false}"
val resp = parse_claude_json_response(json)
# JSON objects are backed by a key-sorted dict, so the re-serialized
# member order is not insertion order; assert the members, not the order.
expect(resp.content.len()).to_equal(
    "{\"name\":\"Simple\",\"items\":[1,2],\"note\":\"brace } text\"}".len()
)
expect(resp.content).to_contain("\"name\":\"Simple\"")
expect(resp.content).to_contain("\"items\":[1,2]")
expect(resp.content).to_contain("\"note\":\"brace } text\"")
```

</details>

#### should accept legal whitespace around object separators

- should accept legal whitespace around object separators
- Verify: should accept legal whitespace around object separators
   - Expected: resp.content equals `spaced`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should accept legal whitespace around object separators")
step("Verify: should accept legal whitespace around object separators")
val json = "{ \"result\" : \"spaced\", \"is_error\" : false }"
val resp = parse_claude_json_response(json)
expect(resp.is_error).to_be(false)
expect(resp.content).to_equal("spaced")
```

</details>

#### should preserve scalar structured output as JSON

- should preserve scalar structured output as JSON
- Verify: should preserve scalar structured output as JSON
   - Expected: text_value.content equals `"answer"`
   - Expected: null_value.content equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should preserve scalar structured output as JSON")
step("Verify: should preserve scalar structured output as JSON")
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

### parse_claude_stream_line

#### should parse content_block_delta

- should parse content_block_delta
- Verify: should parse content_block_delta
   - Expected: evt.event_type equals `content_block_delta`
   - Expected: evt.content equals `Hello `


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse content_block_delta")
step("Verify: should parse content_block_delta")
val line = mock_stream_line("content_block_delta", "Hello ")
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("content_block_delta")
expect(evt.content).to_equal("Hello ")
```

</details>

#### should unescape streamed text deltas

- should unescape streamed text deltas
- Verify: should unescape streamed text deltas
   - Expected: evt.content equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should unescape streamed text deltas")
step("Verify: should unescape streamed text deltas")
val expected = "first\nsecond"
val line = mock_stream_line("content_block_delta", expected)
val evt = parse_claude_stream_line(line)
expect(evt.content).to_equal(expected)
```

</details>

#### should parse message_stop

- should parse message_stop
- Verify: should parse message_stop
   - Expected: evt.event_type equals `message_stop`
   - Expected: evt.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse message_stop")
step("Verify: should parse message_stop")
var line = LB()
line = line + Q() + "type" + Q() + ":" + Q() + "message_stop" + Q() + ","
line = line + Q() + "stop_reason" + Q() + ":" + Q() + "end_turn" + Q()
line = line + RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("message_stop")
expect(evt.stop_reason).to_equal("end_turn")
```

</details>

#### should parse message_start with model

- should parse message_start with model
- Verify: should parse message_start with model
   - Expected: evt.event_type equals `message_start`
   - Expected: evt.model equals `claude-sonnet-4-20250514`
   - Expected: evt.input_tokens equals `25`
   - Expected: evt.output_tokens equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse message_start with model")
step("Verify: should parse message_start with model")
var line = LB()
line = line + Q() + "type" + Q() + ":" + Q() + "message_start" + Q() + ","
line = line + Q() + "message" + Q() + ":{"
line = line + Q() + "model" + Q() + ":" + Q() + "claude-sonnet-4-20250514" + Q() + ","
line = line + Q() + "usage" + Q() + ":{"
line = line + Q() + "input_tokens" + Q() + ":25,"
line = line + Q() + "output_tokens" + Q() + ":1}" + RB()
line = line + RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("message_start")
expect(evt.model).to_equal("claude-sonnet-4-20250514")
expect(evt.input_tokens).to_equal(25)  # oracle: 25 — named expected value from the requirement
expect(evt.output_tokens).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### should parse message_delta usage and stop reason

- should parse message_delta usage and stop reason
- Verify: should parse message_delta usage and stop reason
   - Expected: evt.event_type equals `message_delta`
   - Expected: evt.stop_reason equals `end_turn`
   - Expected: evt.output_tokens equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse message_delta usage and stop reason")
step("Verify: should parse message_delta usage and stop reason")
val line = "{\"type\":\"message_delta\",\"delta\":{\"stop_reason\":\"end_turn\"},\"usage\":{\"output_tokens\":15}" + RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("message_delta")
expect(evt.stop_reason).to_equal("end_turn")
expect(evt.output_tokens).to_equal(15)  # oracle: 15 — named expected value from the requirement
```

</details>

#### should parse a Claude Code system init envelope

- should parse a Claude Code system init envelope
- Verify: should parse a Claude Code system init envelope
   - Expected: evt.event_type equals `system`
   - Expected: evt.session_id equals `session-init`
   - Expected: evt.model equals `claude-sonnet-4-6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse a Claude Code system init envelope")
step("Verify: should parse a Claude Code system init envelope")
val line = "{\"type\":\"system\",\"subtype\":\"init\",\"session_id\":\"session-init\",\"model\":\"claude-sonnet-4-6\"}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("system")
expect(evt.session_id).to_equal("session-init")
expect(evt.model).to_equal("claude-sonnet-4-6")
```

</details>

#### should parse a Claude Code assistant envelope

- should parse a Claude Code assistant envelope
- Verify: should parse a Claude Code assistant envelope
   - Expected: evt.event_type equals `assistant`
   - Expected: evt.content equals `Hello from Claude`
   - Expected: evt.session_id equals `session-a`
   - Expected: evt.input_tokens equals `12`
   - Expected: evt.output_tokens equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse a Claude Code assistant envelope")
step("Verify: should parse a Claude Code assistant envelope")
val line = "{\"type\":\"assistant\",\"message\":{\"model\":\"claude-sonnet-4-6\",\"content\":[{\"type\":\"text\",\"text\":\"Hello from Claude\"}],\"usage\":{\"input_tokens\":12,\"output_tokens\":4}" + RB() + ",\"session_id\":\"session-a\"}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("assistant")
expect(evt.content).to_equal("Hello from Claude")
expect(evt.session_id).to_equal("session-a")
expect(evt.input_tokens).to_equal(12)  # oracle: 12 — named expected value from the requirement
expect(evt.output_tokens).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### should aggregate every assistant text block

- should aggregate every assistant text block
- Verify: should aggregate every assistant text block
   - Expected: evt.content equals `one two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should aggregate every assistant text block")
step("Verify: should aggregate every assistant text block")
val line = "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"text\",\"text\":\"one\"},{\"type\":\"tool_use\",\"name\":\"Read\"},{\"type\":\"text\",\"text\":\" two\"}]}" + RB()
val evt = parse_claude_stream_line(line)
expect(evt.content).to_equal("one two")
```

</details>

#### should parse a Claude Code result envelope

- should parse a Claude Code result envelope
- Verify: should parse a Claude Code result envelope
   - Expected: evt.event_type equals `result`
   - Expected: evt.content equals `done`
   - Expected: evt.session_id equals `session-r`
   - Expected: evt.stop_reason equals `end_turn`
   - Expected: evt.input_tokens equals `20`
   - Expected: evt.output_tokens equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse a Claude Code result envelope")
step("Verify: should parse a Claude Code result envelope")
val line = "{\"type\":\"result\",\"subtype\":\"success\",\"is_error\":false,\"result\":\"done\",\"session_id\":\"session-r\",\"stop_reason\":\"end_turn\",\"usage\":{\"input_tokens\":20,\"output_tokens\":6}" + RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("result")
expect(evt.content).to_equal("done")
expect(evt.session_id).to_equal("session-r")
expect(evt.stop_reason).to_equal("end_turn")
expect(evt.input_tokens).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(evt.output_tokens).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

#### should reject malformed stream result contracts

- should reject malformed stream result contracts
- Verify: should reject malformed stream result contracts
   - Expected: bad_flag.stop_reason equals `invalid`
   - Expected: bad_result.stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject malformed stream result contracts")
step("Verify: should reject malformed stream result contracts")
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

#### should default message stop and reject malformed stream metadata

- should default message stop and reject malformed stream metadata
- Verify: should default message stop and reject malformed stream metadata
   - Expected: stopped.stop_reason equals `end_turn`
   - Expected: root_model.stop_reason equals `invalid`
   - Expected: nested_model.stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should default message stop and reject malformed stream metadata")
step("Verify: should default message stop and reject malformed stream metadata")
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
    "{\"type\":\"assistant\",\"message\":{\"model\":42,\"content\":[]}" + RB()
)
expect(nested_model.stop_reason).to_equal("invalid")
expect(nested_model.content).to_contain("message model")
```

</details>

#### should reject malformed assistant content and usage values

- should reject malformed assistant content and usage values
- Verify: should reject malformed assistant content and usage values
   - Expected: scalar_content.stop_reason equals `invalid`
   - Expected: bad_block.stop_reason equals `invalid`
   - Expected: fractional_usage.stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject malformed assistant content and usage values")
step("Verify: should reject malformed assistant content and usage values")
val scalar_content = parse_claude_stream_line(
    "{\"type\":\"assistant\",\"message\":{\"content\":\"text\"}" + RB()
)
expect(scalar_content.stop_reason).to_equal("invalid")
expect(scalar_content.content).to_contain("must be an array")
val bad_block = parse_claude_stream_line(
    "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"text\",\"text\":42}]}" + RB()
)
expect(bad_block.stop_reason).to_equal("invalid")
expect(bad_block.content).to_contain("typed objects")
val fractional_usage = parse_claude_stream_line(
    "{\"type\":\"result\",\"is_error\":false,\"result\":\"done\",\"usage\":{\"output_tokens\":2.5}" + RB()
)
expect(fractional_usage.stop_reason).to_equal("invalid")
expect(fractional_usage.content).to_contain("non-negative integers")
```

</details>

#### should parse structured output from a Claude Code result envelope

- should parse structured output from a Claude Code result envelope
- Verify: should parse structured output from a Claude Code result envelope
   - Expected: evt.event_type equals `result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse structured output from a Claude Code result envelope")
step("Verify: should parse structured output from a Claude Code result envelope")
val line = "{\"type\":\"result\",\"subtype\":\"success\",\"is_error\":false,\"structured_output\":{\"answer\":42,\"labels\":[\"a\",\"b\"]},\"session_id\":\"session-r\"}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("result")
expect(evt.content).to_equal(
    "{\"answer\":42,\"labels\":[\"a\",\"b\"]}"
)
```

</details>

#### should parse a streaming error envelope

- should parse a streaming error envelope
- Verify: should parse a streaming error envelope
   - Expected: evt.event_type equals `error`
   - Expected: evt.content equals `Overloaded`
   - Expected: evt.stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should parse a streaming error envelope")
step("Verify: should parse a streaming error envelope")
val line = "{\"type\":\"error\",\"error\":{\"type\":\"overloaded_error\",\"message\":\"Overloaded\"}" + RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("error")
expect(evt.content).to_equal("Overloaded")
expect(evt.stop_reason).to_equal("error")
```

</details>

#### should redact secrets in streaming protocol errors

- should redact secrets in streaming protocol errors
- Verify: should redact secrets in streaming protocol errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should redact secrets in streaming protocol errors")
step("Verify: should redact secrets in streaming protocol errors")
val line = "{\"type\":\"error\",\"error\":{\"message\":\"failed sk-ant-fixture-secret\"}" + RB()
val evt = parse_claude_stream_line(line)
expect(evt.content.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

#### should redact secrets in error result envelopes

- should redact secrets in error result envelopes
- Verify: should redact secrets in error result envelopes
   - Expected: evt.stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should redact secrets in error result envelopes")
step("Verify: should redact secrets in error result envelopes")
val line = "{\"type\":\"result\",\"is_error\":true,\"result\":\"failed sk-ant-fixture-secret\"}"
val evt = parse_claude_stream_line(line)
expect(evt.content.contains("sk-ant-fixture-secret")).to_be(false)
expect(evt.stop_reason).to_equal("error")
```

</details>

#### should preserve a nested diagnostic from an error-only result

- should preserve a nested diagnostic from an error-only result
- Verify: should preserve a nested diagnostic from an error-only result
   - Expected: evt.event_type equals `result`
   - Expected: evt.content equals `provider overloaded`
   - Expected: evt.stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should preserve a nested diagnostic from an error-only result")
step("Verify: should preserve a nested diagnostic from an error-only result")
val line = "{\"type\":\"result\",\"is_error\":true,\"error\":{\"message\":\"provider overloaded\"}" + RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("result")
expect(evt.content).to_equal("provider overloaded")
expect(evt.stop_reason).to_equal("error")
```

</details>

#### should accept a string protocol error and redact it

- should accept a string protocol error and redact it
- Verify: should accept a string protocol error and redact it
   - Expected: evt.event_type equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should accept a string protocol error and redact it")
step("Verify: should accept a string protocol error and redact it")
val line = "{\"type\":\"error\",\"error\":\"failed sk-ant-fixture-secret\"}"
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("error")
expect(evt.content).to_contain("[REDACTED:")
expect(evt.content.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

#### should reject malformed nested stream fields

- should reject malformed nested stream fields
- Verify: should reject malformed nested stream fields
   - Expected: nested_usage.stop_reason equals `invalid`
   - Expected: scalar_delta.stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject malformed nested stream fields")
step("Verify: should reject malformed nested stream fields")
val nested_usage = parse_claude_stream_line(
    "{\"type\":\"assistant\",\"message\":{\"usage\":{\"input_tokens\":\"many\"}" + RB() + RB()
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

#### should preserve explicit zero stream usage and partial JSON

- should preserve explicit zero stream usage and partial JSON
- Verify: should preserve explicit zero stream usage and partial JSON
   - Expected: started.input_tokens equals `0`
   - Expected: delta.content equals `{"x":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should preserve explicit zero stream usage and partial JSON")
step("Verify: should preserve explicit zero stream usage and partial JSON")
val started = parse_claude_stream_line(
    "{\"type\":\"message_start\",\"input_tokens\":0,\"message\":{\"usage\":{\"input_tokens\":9}" + RB() + RB()
)
expect(started.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
val delta = parse_claude_stream_line(
    "{\"type\":\"content_block_delta\",\"delta\":{\"partial_json\":\"{\\\"x\\\":\"}" + RB()
)
expect(delta.content).to_equal("{\"x\":")
```

</details>

#### should accept non-content protocol events without forging terminal state

- should accept non-content protocol events without forging terminal state
- Verify: should accept non-content protocol events without forging terminal state
   - Expected: evt.event_type equals `event_type`
   - Expected: evt.stop_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should accept non-content protocol events without forging terminal state")
step("Verify: should accept non-content protocol events without forging terminal state")
for event_type in ["content_block_start", "content_block_stop", "ping", "user", "rate_limit_event"]:
    val evt = parse_claude_stream_line(
        "{\"type\":\"" + event_type + "\"}"
    )
    expect(evt.event_type).to_equal(event_type)
    expect(evt.stop_reason).to_equal("")
```

</details>

#### should handle empty line

- should handle empty line
- Verify: should handle empty line
   - Expected: evt.event_type equals `empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should handle empty line")
step("Verify: should handle empty line")
val evt = parse_claude_stream_line("")
expect(evt.event_type).to_equal("empty")
```

</details>

#### should reject an event without a type

- should reject an event without a type
- Verify: should reject an event without a type
   - Expected: evt.event_type equals `error`
   - Expected: evt.stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject an event without a type")
step("Verify: should reject an event without a type")
var line = LB()
line = line + Q() + "data" + Q() + ":" + Q() + "something" + Q()
line = line + RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("error")
expect(evt.stop_reason).to_equal("invalid")
```

</details>

#### should reject malformed stream JSON

- should reject malformed stream JSON
- Verify: should reject malformed stream JSON
   - Expected: evt.event_type equals `error`
   - Expected: evt.stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject malformed stream JSON")
step("Verify: should reject malformed stream JSON")
val evt = parse_claude_stream_line("not-json")
expect(evt.event_type).to_equal("error")
expect(evt.stop_reason).to_equal("invalid")
```

</details>

#### should reject unsupported typed stream events

- should reject unsupported typed stream events
- Verify: should reject unsupported typed stream events
   - Expected: evt.event_type equals `error`
   - Expected: evt.stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject unsupported typed stream events")
step("Verify: should reject unsupported typed stream events")
val evt = parse_claude_stream_line(
    "{\"type\":\"forged_terminal\",\"result\":\"done\"}"
)
expect(evt.event_type).to_equal("error")
expect(evt.stop_reason).to_equal("invalid")
expect(evt.content).to_contain("unsupported")
```

</details>

#### should reject a contract-free result event

- should reject a contract-free result event
- Verify: should reject a contract-free result event
   - Expected: evt.event_type equals `error`
   - Expected: evt.stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject a contract-free result event")
step("Verify: should reject a contract-free result event")
val evt = parse_claude_stream_line("{\"type\":\"result\"}")
expect(evt.event_type).to_equal("error")
expect(evt.stop_reason).to_equal("invalid")
expect(evt.content).to_contain("missing result")
```

</details>

### claude_cli_send - local fixture

#### should forward advanced arguments and preserve response metadata

- should forward advanced arguments and preserve response metadata
- Verify: should forward advanced arguments and preserve response metadata
   - Expected: resp.error equals ``
   - Expected: resp.content equals `advanced-ok`
   - Expected: resp.model equals `sonnet`
   - Expected: resp.session_id equals `advanced-session`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should forward advanced arguments and preserve response metadata")
step("Verify: should forward advanced arguments and preserve response metadata")
# The fixture fails closed (exit 70) unless the resume session,
# max_turns and the FULL tool vector are forwarded.
val resp = claude_cli_send(
    MOCK_CLAUDE_CLI, "fixture-advanced", "sonnet", "", "advanced-resume", 3, 0,
    "{\"type\":\"object\"}", ["Read", "Write"], ["--fixture-extra"]
)
expect(resp.is_error).to_be(false)
expect(resp.error).to_equal("")
expect(resp.content).to_equal("advanced-ok")
expect(resp.model).to_equal("sonnet")
expect(resp.session_id).to_equal("advanced-session")
```

</details>

#### should fail closed and redact subprocess diagnostics

- should fail closed and redact subprocess diagnostics
- Verify: should fail closed and redact subprocess diagnostics
   - Expected: comparison.status equals `EvidenceStatus.passed`
   - Expected: failed.stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should fail closed and redact subprocess diagnostics")
step("Verify: should fail closed and redact subprocess diagnostics")
val malformed = claude_cli_send(
    MOCK_CLAUDE_CLI, "fixture-json-malformed", "sonnet",
    "", "", 0, 0, "", [], []
)
expect(malformed.is_error).to_be(true)
expect(malformed.error).to_contain("invalid JSON")

val capture = UntypedCapture(label: "claude-cli-malformed-json-error", raw_value: malformed.error, source_kind: "stdout")
val evidence = untyped_capture_to_canonical(capture, "claude_cli_spec/malformed-json-error")
val comparison = compare_evidence(evidence, oracle_spec("claude_cli_spec/malformed-json-error", [
    check_exact("value", "invalid JSON response from claude CLI")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)

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

### claude_cli_stream - local fixture

#### should return a complete ordered stream

- should return a complete ordered stream
- Verify: should return a complete ordered stream
   - Expected: events.len() equals `3`
   - Expected: events[0].event_type equals `system`
   - Expected: events[0].session_id equals `stream-session`
   - Expected: events[1].event_type equals `assistant`
   - Expected: events[1].content equals `streamed fixture`
   - Expected: events[2].event_type equals `result`
   - Expected: events[2].content equals `stream complete`
   - Expected: events[2].output_tokens equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should return a complete ordered stream")
step("Verify: should return a complete ordered stream")
val events = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream", "sonnet",
    "Be concise", "", 1
)
expect(events.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(events[0].event_type).to_equal("system")
expect(events[0].session_id).to_equal("stream-session")
expect(events[1].event_type).to_equal("assistant")
expect(events[1].content).to_equal("streamed fixture")
expect(events[2].event_type).to_equal("result")
expect(events[2].content).to_equal("stream complete")
expect(events[2].output_tokens).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### should return one redacted terminal error for a failed subprocess

- should return one redacted terminal error for a failed subprocess
- Verify: should return one redacted terminal error for a failed subprocess
   - Expected: events.len() equals `1`
   - Expected: events[0].event_type equals `error`
   - Expected: events[0].stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should return one redacted terminal error for a failed subprocess")
step("Verify: should return one redacted terminal error for a failed subprocess")
val events = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-error", "sonnet", "", "", 1
)
expect(events.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(events[0].event_type).to_equal("error")
expect(events[0].stop_reason).to_equal("error")
expect(events[0].content).to_contain("exited with code 7")
expect(events[0].content).to_contain("[REDACTED:")
expect(events[0].content.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

#### should return a redacted terminal error result from the stream fixture

- should return a redacted terminal error result from the stream fixture
- Verify: should return a redacted terminal error result from the stream fixture
   - Expected: events.len() equals `1`
   - Expected: events[0].event_type equals `result`
   - Expected: events[0].stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should return a redacted terminal error result from the stream fixture")
step("Verify: should return a redacted terminal error result from the stream fixture")
val events = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-secret-error", "sonnet", "", "", 1
)
expect(events.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(events[0].event_type).to_equal("result")
expect(events[0].stop_reason).to_equal("error")
expect(events[0].content).to_contain("[REDACTED:")
expect(events[0].content.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

#### should return a redacted terminal provider error from the stream fixture

- should return a redacted terminal provider error from the stream fixture
- Verify: should return a redacted terminal provider error from the stream fixture
   - Expected: events.len() equals `1`
   - Expected: events[0].event_type equals `error`
   - Expected: events[0].stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should return a redacted terminal provider error from the stream fixture")
step("Verify: should return a redacted terminal provider error from the stream fixture")
val events = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-provider-error", "sonnet", "", "", 1
)
expect(events.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(events[0].event_type).to_equal("error")
expect(events[0].stop_reason).to_equal("error")
expect(events[0].content).to_contain("[REDACTED:")
expect(events[0].content.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

#### should reject malformed and duplicate terminal streams

- should reject malformed and duplicate terminal streams
- Verify: should reject malformed and duplicate terminal streams
   - Expected: malformed.len() equals `1`
   - Expected: malformed[0].stop_reason equals `invalid`
   - Expected: duplicate.len() equals `1`
   - Expected: duplicate[0].stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject malformed and duplicate terminal streams")
step("Verify: should reject malformed and duplicate terminal streams")
val malformed = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-malformed-then-result",
    "sonnet", "", "", 1
)
expect(malformed.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(malformed[0].stop_reason).to_equal("invalid")
expect(malformed[0].content).to_contain("invalid JSON")

val duplicate = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-duplicate-terminal",
    "sonnet", "", "", 1
)
expect(duplicate.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(duplicate[0].stop_reason).to_equal("invalid")
expect(duplicate[0].content).to_contain("after a terminal")
```

</details>

#### should reject an assistant event after message stop

- should reject an assistant event after message stop
- Verify: should reject an assistant event after message stop
   - Expected: events.len() equals `1`
   - Expected: events[0].event_type equals `error`
   - Expected: events[0].stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject an assistant event after message stop")
step("Verify: should reject an assistant event after message stop")
val events = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-stop-then-assistant",
    "sonnet", "", "", 1
)
expect(events.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(events[0].event_type).to_equal("error")
expect(events[0].stop_reason).to_equal("invalid")
expect(events[0].content).to_contain("after message_stop")
```

</details>

#### should distinguish incomplete, empty, and valid stop-result streams

- should distinguish incomplete, empty, and valid stop-result streams
- Verify: should distinguish incomplete, empty, and valid stop-result streams
   - Expected: incomplete.len() equals `2`
   - Expected: incomplete[1].event_type equals `error`
   - Expected: empty.len() equals `1`
   - Expected: completed.len() equals `2`
   - Expected: completed[0].event_type equals `message_stop`
   - Expected: completed[1].event_type equals `result`
   - Expected: completed[1].content equals `complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should distinguish incomplete, empty, and valid stop-result streams")
step("Verify: should distinguish incomplete, empty, and valid stop-result streams")
val incomplete = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-incomplete",
    "sonnet", "", "", 1
)
expect(incomplete.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(incomplete[1].event_type).to_equal("error")
expect(incomplete[1].content).to_contain("before a terminal event")

val empty = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-empty", "sonnet", "", "", 1
)
expect(empty.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(empty[0].content).to_contain("no valid stream events")

val completed = claude_cli_stream(
    MOCK_CLAUDE_CLI, "fixture-stream-stop-then-result",
    "sonnet", "", "", 1
)
expect(completed.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(completed[0].event_type).to_equal("message_stop")
expect(completed[1].event_type).to_equal("result")
expect(completed[1].content).to_equal("complete")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 84 |
| Active scenarios | 84 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-APP-LLM-CARET-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ec67349b2c8166dc86b58d04e31511395ebcdba891e7a2349bffa0977d291eeb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec67349b2c8166dc86b58d04e31511395ebcdba891e7a2349bffa0977d291eeb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec67349b2c8166dc86b58d04e31511395ebcdba891e7a2349bffa0977d291eeb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/llm_caret/claude_cli_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_cli_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/claude_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_cli_spec.spl:98:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include prompt with -p flag' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/claude_cli_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include prompt with -p flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_cli_spec.spl:107:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should default to json output format' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/claude_cli_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should default to json output format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_cli_spec.spl:114:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have no model flag when empty' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/claude_cli_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should have no model flag when empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_cli_spec.spl:121:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have no system-prompt flag when empty' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/claude_cli_spec.spl:128:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have no resume flag when empty' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/claude_cli_spec.spl:136:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include model flag' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
