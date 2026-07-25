# LLM Caret Claude API Exchange

The 13 scenarios below exercise the shipped Claude API request builder,
deterministic completion boundary, parser, missing-key guard, and static
production send delegation. They use no live network or provider.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 13 | 13 | 0 | 0 |

## Scenarios

#### should build the exact default Claude API request

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val messages = "[{\"role\":\"user\",\"content\":\"Hello\"}]"
step("Build or complete the production exchange")
val request = build_claude_api_request("sk-test", "https://api.anthropic.com", "", messages, "", 0)
step("Check exact request response and error state")
expect(request.method).to_equal("POST")
expect(request.url).to_equal("https://api.anthropic.com/v1/messages")
expect(request.headers).to_equal("x-api-key: sk-test\nanthropic-version: 2023-06-01\ncontent-type: application/json")
expect(request.body).to_equal("{\"model\":\"claude-sonnet-4-20250514\",\"max_tokens\":4096,\"messages\":[{\"role\":\"user\",\"content\":\"Hello\"}]}")
```

</details>

#### should normalize absent single and repeated base URL slashes

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val messages = "[]"
step("Build or complete the production exchange")
val absent = build_claude_api_request("key", "https://example.test", "model", messages, "", 1)
val single = build_claude_api_request("key", "https://example.test/", "model", messages, "", 1)
val repeated = build_claude_api_request("key", "https://example.test///", "model", messages, "", 1)
step("Check exact request response and error state")
expect(absent.url).to_equal("https://example.test/v1/messages")
expect(single.url).to_equal(absent.url)
expect(repeated.url).to_equal(absent.url)
```

</details>

#### should include exact overrides and escape model and system text

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val model = "claude\"custom\\model"
val system = "line one\nline \"two\"\tend"
step("Build or complete the production exchange")
val request = build_claude_api_request("key", "https://example.test", model, "[]", system, 8192)
step("Check exact request response and error state")
expect(request.body).to_equal("{\"model\":\"claude\\\"custom\\\\model\",\"max_tokens\":8192,\"system\":\"line one\\nline \\\"two\\\"\\tend\",\"messages\":[]}")
```

</details>

#### should escape exact role and content text in one message

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val role = "user\"role"
val content = "slash\\ quote\" newline\nreturn\rtab\t"
step("Build or complete the production exchange")
val messages = build_single_message_json(role, content)
step("Check exact request response and error state")
expect(messages).to_equal("[{\"role\":\"user\\\"role\",\"content\":\"slash\\\\ quote\\\" newline\\nreturn\\rtab\\t\"}]")
```

</details>

#### should preserve exact successful response fields

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val raw = "{\"type\":\"message\",\"content\":[{\"type\":\"text\",\"text\":\"Hello back\"}],\"model\":\"claude-sonnet-4-20250514\",\"stop_reason\":\"end_turn\",\"usage\":{\"input_tokens\":12,\"output_tokens\":7}}"
step("Build or complete the production exchange")
val response = complete_claude_api_exchange(raw, "")
step("Check exact request response and error state")
expect(response.content).to_equal("Hello back")
expect(response.model).to_equal("claude-sonnet-4-20250514")
expect(response.stop_reason).to_equal("end_turn")
expect(response.input_tokens).to_equal(12)
expect(response.output_tokens).to_equal(7)
expect(response.error).to_equal("")
expect(response.is_error).to_equal(false)
expect(response.raw).to_equal(raw)
```

</details>

#### should expose API error messages and preserve their raw body

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val raw = "{\"type\":\"error\",\"error\":{\"type\":\"authentication_error\",\"message\":\"invalid x-api-key\"}}"
step("Build or complete the production exchange")
val response = complete_claude_api_exchange(raw, "")
step("Check exact request response and error state")
expect(response.content).to_equal("")
expect(response.stop_reason).to_equal("error")
expect(response.error).to_equal("invalid x-api-key")
expect(response.is_error).to_equal(true)
expect(response.raw).to_equal(raw)
```

</details>

#### should reject an empty response

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val raw = ""
step("Build or complete the production exchange")
val response = complete_claude_api_exchange(raw, "")
step("Check exact request response and error state")
expect(response.error).to_equal("empty response")
expect(response.is_error).to_equal(true)
expect(response.raw).to_equal("")
```

</details>

#### should reject malformed non-JSON and fieldless responses

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val nonJsonRaw = "not-json"
val fieldlessRaw = "{}"
val unterminatedRaw = "{\"type\":\"message\",\"text\":\"unterminated}"
step("Build or complete the production exchange")
val nonJson = complete_claude_api_exchange(nonJsonRaw, "")
val fieldless = complete_claude_api_exchange(fieldlessRaw, "")
val unterminated = complete_claude_api_exchange(unterminatedRaw, "")
step("Check exact request response and error state")
expect(nonJson.error).to_equal("malformed response")
expect(nonJson.is_error).to_equal(true)
expect(nonJson.raw).to_equal(nonJsonRaw)
expect(fieldless.error).to_equal("malformed response")
expect(fieldless.is_error).to_equal(true)
expect(fieldless.raw).to_equal(fieldlessRaw)
expect(unterminated.error).to_equal("malformed response")
expect(unterminated.is_error).to_equal(true)
expect(unterminated.raw).to_equal(unterminatedRaw)
```

</details>

#### should reject a non-string content text field

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val raw = "{\"type\":\"message\",\"content\":[{\"type\":\"text\",\"text\":123}]}"
step("Build or complete the production exchange")
val response = complete_claude_api_exchange(raw, "")
step("Check exact request response and error state")
expect(response.error).to_equal("malformed response")
expect(response.is_error).to_equal(true)
expect(response.raw).to_equal(raw)
```

</details>

#### should default stop reason and token counts for valid empty text

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val raw = "{\"text\":\"\"}"
step("Build or complete the production exchange")
val response = complete_claude_api_exchange(raw, "")
step("Check exact request response and error state")
expect(response.content).to_equal("")
expect(response.model).to_equal("")
expect(response.stop_reason).to_equal("end_turn")
expect(response.input_tokens).to_equal(0)
expect(response.output_tokens).to_equal(0)
expect(response.error).to_equal("")
expect(response.is_error).to_equal(false)
expect(response.raw).to_equal(raw)
```

</details>

#### should preserve injected transport errors and raw bodies

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val raw = "{\"proxy\":\"offline\"}"
step("Build or complete the production exchange")
val response = complete_claude_api_exchange(raw, "connection refused")
step("Check exact request response and error state")
expect(response.content).to_equal("")
expect(response.stop_reason).to_equal("error")
expect(response.input_tokens).to_equal(0)
expect(response.output_tokens).to_equal(0)
expect(response.error).to_equal("HTTP error: connection refused")
expect(response.is_error).to_equal(true)
expect(response.raw).to_equal(raw)
```

</details>

#### should fail closed before transport when the API key is absent

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val apiKey = ""
step("Build or complete the production exchange")
val response = claude_api_send(apiKey, "https://api.anthropic.com", "", "[]", "", 0)
step("Check exact request response and error state")
expect(response.content).to_equal("")
expect(response.stop_reason).to_equal("error")
expect(response.error).to_equal("ANTHROPIC_API_KEY not set")
expect(response.is_error).to_equal(true)
expect(response.raw).to_equal("")
```

</details>

#### should delegate production send through build retry transport and complete

<details>
<summary>Executable SSpec</summary>

```simple
step("Prepare Claude API request inputs")
val source = rt_file_read_text("src/app/llm_caret/claude_api.spl") ?? ""
step("Build or complete the production exchange")
val sendParts = source.split("fn claude_api_send(")
val transportCallParts = sendParts[1].split("http_request_raw(")
step("Check exact request response and error state")
expect(sendParts.len()).to_equal(2)
expect(transportCallParts.len()).to_equal(2)
expect(sendParts[1]).to_contain("val request = build_claude_api_request(api_key, base_url, model, messages_json, system_prompt, max_tokens)")
expect(sendParts[1]).to_contain("val policy = retry_policy_from_env()")
expect(sendParts[1]).to_contain("val outcome = with_retry(policy, fn(attempt: i64) -> (i64, text, text, i64):")
expect(sendParts[1]).to_contain("val result = http_request_raw(request.method, request.url, request.headers, request.body)")
expect(sendParts[1]).to_contain("complete_claude_api_exchange(outcome.body, outcome.error)")
expect(sendParts[1].index_of("build_claude_api_request")).to_be_less_than(sendParts[1].index_of("retry_policy_from_env"))
expect(sendParts[1].index_of("retry_policy_from_env")).to_be_less_than(sendParts[1].index_of("with_retry"))
expect(sendParts[1].index_of("with_retry")).to_be_less_than(sendParts[1].index_of("http_request_raw"))
expect(sendParts[1].index_of("http_request_raw")).to_be_less_than(sendParts[1].index_of("complete_claude_api_exchange"))
```

</details>

## Evidence boundary

The pure request/completion scenarios prove deterministic request and response
behavior. The source scenario proves the shipped send function builds once,
owns retry policy, contains one textual `http_request_raw` call expression per
retry callback attempt, and completes from the retry outcome. It does not claim
one total network attempt. No scenario performs a live network exchange,
exercises Anthropic credentials, or claims retry timing, provider availability,
latency, or RSS evidence.
