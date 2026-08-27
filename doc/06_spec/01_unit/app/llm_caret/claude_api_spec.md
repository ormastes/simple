# LLM Caret Claude API Exchange

> Purpose: Prove that LLM Caret Claude API exchange.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Claude API Exchange

Purpose: Prove that LLM Caret Claude API exchange.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that LLM Caret Claude API exchange.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### LLM Caret Claude API exchange

### supporting request construction

#### should build the exact default Claude API request

- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: request.method equals `POST`
   - Expected: request.url equals `https://api.anthropic.com/v1/messages`
   - Expected: request.headers equals `x-api-key: sk-test\nanthropic-version: 2023-06-01\ncontent-type: application/... (full value in folded executable source)`
   - Expected: request.body equals `{"model":"claude-sonnet-4-20250514","max_tokens":4096,"messages":[{"role":"us... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-LLM-CARET-001
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

- should normalize absent single and repeated base URL slashes
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: absent.url equals `https://example.test/v1/messages`
   - Expected: single.url equals `absent.url`
   - Expected: repeated.url equals `absent.url`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should normalize absent single and repeated base URL slashes")
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

- should include exact overrides and escape model and system text
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: request.body equals `{"model":"claude\\"custom\\\\model","max_tokens":8192,"system":"line one\\nli... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include exact overrides and escape model and system text")
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

- should escape exact role and content text in one message
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: messages equals `[{"role":"user\\"role","content":"slash\\\\ quote\\" newline\\nreturn\\rtab\\... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should escape exact role and content text in one message")
step("Prepare Claude API request inputs")
val role = "user\"role"
val content = "slash\\ quote\" newline\nreturn\rtab\t"
step("Build or complete the production exchange")
val messages = build_single_message_json(role, content)
step("Check exact request response and error state")
expect(messages).to_equal("[{\"role\":\"user\\\"role\",\"content\":\"slash\\\\ quote\\\" newline\\nreturn\\rtab\\t\"}]")
```

</details>

### supporting response completion

#### should preserve exact successful response fields

- should preserve exact successful response fields
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: response.content equals `Hello back`
   - Expected: response.model equals `claude-sonnet-4-20250514`
   - Expected: response.stop_reason equals `end_turn`
   - Expected: response.input_tokens equals `12`
   - Expected: response.output_tokens equals `7`
   - Expected: response.error equals ``
   - Expected: response.is_error is false
   - Expected: response.raw equals `raw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should preserve exact successful response fields")
step("Prepare Claude API request inputs")
val raw = "{\"type\":\"message\",\"content\":[{\"type\":\"text\",\"text\":\"Hello back\"}],\"model\":\"claude-sonnet-4-20250514\",\"stop_reason\":\"end_turn\",\"usage\":{\"input_tokens\":12,\"output_tokens\":7}}"
step("Build or complete the production exchange")
val response = complete_claude_api_exchange(raw, "")
step("Check exact request response and error state")
expect(response.content).to_equal("Hello back")
expect(response.model).to_equal("claude-sonnet-4-20250514")
expect(response.stop_reason).to_equal("end_turn")
expect(response.input_tokens).to_equal(12)  # oracle: 12 — named expected value from the requirement
expect(response.output_tokens).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(response.error).to_equal("")
expect(response.is_error).to_equal(false)
expect(response.raw).to_equal(raw)
```

</details>

#### should expose API error messages and preserve their raw body

- should expose API error messages and preserve their raw body
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: response.content equals ``
   - Expected: response.stop_reason equals `error`
   - Expected: response.error equals `invalid x-api-key`
   - Expected: response.is_error is true
   - Expected: response.raw equals `raw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should expose API error messages and preserve their raw body")
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

- should reject an empty response
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: response.error equals `empty response`
   - Expected: response.is_error is true
   - Expected: response.raw equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject an empty response")
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

- should reject malformed non-JSON and fieldless responses
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: nonJson.error equals `malformed response`
   - Expected: nonJson.is_error is true
   - Expected: nonJson.raw equals `nonJsonRaw`
   - Expected: fieldless.error equals `malformed response`
   - Expected: fieldless.is_error is true
   - Expected: fieldless.raw equals `fieldlessRaw`
   - Expected: unterminated.error equals `malformed response`
   - Expected: unterminated.is_error is true
   - Expected: unterminated.raw equals `unterminatedRaw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject malformed non-JSON and fieldless responses")
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

- should reject a non-string content text field
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: response.error equals `malformed response`
   - Expected: response.is_error is true
   - Expected: response.raw equals `raw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject a non-string content text field")
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

- should default stop reason and token counts for valid empty text
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: response.content equals ``
   - Expected: response.model equals ``
   - Expected: response.stop_reason equals `end_turn`
   - Expected: response.input_tokens equals `0`
   - Expected: response.output_tokens equals `0`
   - Expected: response.error equals ``
   - Expected: response.is_error is false
   - Expected: response.raw equals `raw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should default stop reason and token counts for valid empty text")
step("Prepare Claude API request inputs")
val raw = "{\"text\":\"\"}"
step("Build or complete the production exchange")
val response = complete_claude_api_exchange(raw, "")
step("Check exact request response and error state")
expect(response.content).to_equal("")
expect(response.model).to_equal("")
expect(response.stop_reason).to_equal("end_turn")
expect(response.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(response.output_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(response.error).to_equal("")
expect(response.is_error).to_equal(false)
expect(response.raw).to_equal(raw)
```

</details>

#### should preserve injected transport errors and raw bodies

- should preserve injected transport errors and raw bodies
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: response.content equals ``
   - Expected: response.stop_reason equals `error`
   - Expected: response.input_tokens equals `0`
   - Expected: response.output_tokens equals `0`
   - Expected: response.error equals `HTTP error: connection refused`
   - Expected: response.is_error is true
   - Expected: response.raw equals `raw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should preserve injected transport errors and raw bodies")
step("Prepare Claude API request inputs")
val raw = "{\"proxy\":\"offline\"}"
step("Build or complete the production exchange")
val response = complete_claude_api_exchange(raw, "connection refused")
step("Check exact request response and error state")
expect(response.content).to_equal("")
expect(response.stop_reason).to_equal("error")
expect(response.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(response.output_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(response.error).to_equal("HTTP error: connection refused")
expect(response.is_error).to_equal(true)
expect(response.raw).to_equal(raw)
```

</details>

### supporting production send behavior

#### should fail closed before transport when the API key is absent

- should fail closed before transport when the API key is absent
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: response.content equals ``
   - Expected: response.stop_reason equals `error`
   - Expected: response.error equals `ANTHROPIC_API_KEY not set`
   - Expected: response.is_error is true
   - Expected: response.raw equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should fail closed before transport when the API key is absent")
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

- should delegate production send through build retry transport and complete
- Prepare Claude API request inputs
- Build or complete the production exchange
- Check exact request response and error state
   - Expected: sendParts.len() equals `2`
   - Expected: transportHelperParts.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should delegate production send through build retry transport and complete")
step("Prepare Claude API request inputs")
val source = rt_file_read_text("src/app/llm_caret/claude_api.spl") ?? ""
step("Build or complete the production exchange")
val sendParts = source.split("fn claude_api_send(")
val transportHelperParts = source.split("fn claude_api_retry_transport(")
step("Check exact request response and error state")
expect(sendParts.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(transportHelperParts.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(sendParts[1]).to_contain("val request = build_claude_api_request(api_key, base_url, model, messages_json, system_prompt, max_tokens)")
expect(sendParts[1]).to_contain("val policy = retry_policy_from_env()")
expect(sendParts[1]).to_contain("val outcome = with_retry(policy, fn(attempt: i64) -> (i64, text, text, i64):")
expect(sendParts[1]).to_contain("claude_api_retry_transport(request, attempt)")
expect(source).to_contain("fn claude_api_retry_transport(request: ClaudeApiRequest, attempt: i64)")
expect(source).to_contain("val result = http_request_raw(request.method, request.url, request.headers, request.body)")
expect(sendParts[1]).to_contain("complete_claude_api_exchange(outcome.body, outcome.error)")
expect(sendParts[1].index_of("build_claude_api_request")).to_be_less_than(sendParts[1].index_of("retry_policy_from_env"))
expect(sendParts[1].index_of("retry_policy_from_env")).to_be_less_than(sendParts[1].index_of("with_retry"))
expect(sendParts[1].index_of("with_retry")).to_be_less_than(sendParts[1].index_of("claude_api_retry_transport"))
expect(sendParts[1].index_of("claude_api_retry_transport")).to_be_less_than(sendParts[1].index_of("complete_claude_api_exchange"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-LLM-CARET-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c4965bff57c93c9949590bee29d057b063571f4ef2f6c1f5d2086b9bbb10b3cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4965bff57c93c9949590bee29d057b063571f4ef2f6c1f5d2086b9bbb10b3cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4965bff57c93c9949590bee29d057b063571f4ef2f6c1f5d2086b9bbb10b3cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/llm_caret/claude_api_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_api_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/claude_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_api_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build the exact default Claude API request' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/claude_api_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should build the exact default Claude API request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_api_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should normalize absent single and repeated base URL slashes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/claude_api_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should normalize absent single and repeated base URL slashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_api_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include exact overrides and escape model and system text' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/claude_api_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include exact overrides and escape model and system text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_api_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should escape exact role and content text in one message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/claude_api_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve exact successful response fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/claude_api_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose API error messages and preserve their raw body' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
