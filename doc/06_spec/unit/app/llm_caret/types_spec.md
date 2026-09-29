# types_spec

> Purpose: Prove that Message.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# types_spec

Purpose: Prove that Message.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_caret/types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Message.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Message

#### should preserve an explicit role and content

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Construct a production message with an explicit role
   - Expected: msg.role equals `tool`
   - Expected: msg.content equals `result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-LLM-CARET-001
step("Construct a production message with an explicit role")
val msg: Message = new_message("tool", "result")
expect(msg.role).to_equal("tool")
expect(msg.content).to_equal("result")
```

</details>

#### should construct and classify a user message

- should construct and classify a user message
- Construct a production user message
   - Expected: msg.role equals `user`
   - Expected: msg.content equals `Hi there`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct and classify a user message")
step("Construct a production user message")
val msg = new_user_message("Hi there")
expect(msg.role).to_equal("user")
expect(msg.content).to_equal("Hi there")
expect(is_user_message(msg)).to_be(true)
expect(is_assistant_message(msg)).to_be(false)
expect(is_system_message(msg)).to_be(false)
```

</details>

#### should construct and classify an assistant message

- should construct and classify an assistant message
- Construct a production assistant message
   - Expected: msg.role equals `assistant`
   - Expected: msg.content equals `I can help`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct and classify an assistant message")
step("Construct a production assistant message")
val msg = new_assistant_message("I can help")
expect(msg.role).to_equal("assistant")
expect(msg.content).to_equal("I can help")
expect(is_user_message(msg)).to_be(false)
expect(is_assistant_message(msg)).to_be(true)
expect(is_system_message(msg)).to_be(false)
```

</details>

#### should construct and classify a system message

- should construct and classify a system message
- Construct a production system message
   - Expected: msg.role equals `system`
   - Expected: msg.content equals `You are helpful`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct and classify a system message")
step("Construct a production system message")
val msg = new_system_message("You are helpful")
expect(msg.role).to_equal("system")
expect(msg.content).to_equal("You are helpful")
expect(is_user_message(msg)).to_be(false)
expect(is_assistant_message(msg)).to_be(false)
expect(is_system_message(msg)).to_be(true)
```

</details>

### ChatRequest

#### should construct every empty request default

- should construct every empty request default
- Construct a production request without a prompt
   - Expected: req.provider equals ``
   - Expected: req.model equals ``
   - Expected: req.messages.len() equals `0`
   - Expected: req.system_prompt equals ``
   - Expected: req.max_tokens equals `0`
   - Expected: req.session_id equals ``
   - Expected: req.max_turns equals `0`
   - Expected: req.json_schema equals ``
   - Expected: req.tools.len() equals `0`
   - Expected: req.extra_args.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct every empty request default")
step("Construct a production request without a prompt")
val req: ChatRequest = new_chat_request()
expect(req.provider).to_equal("")
expect(req.model).to_equal("")
expect(req.messages.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(req.system_prompt).to_equal("")
expect(req.max_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(req.temperature).to_be_less_than(0.0)
expect(req.session_id).to_equal("")
expect(req.max_turns).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(req.stream).to_be(false)
expect(req.json_schema).to_equal("")
expect(req.tools.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(req.extra_args.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should construct a prompt request with one user message

- should construct a prompt request with one user message
- Construct a production request from a prompt
   - Expected: req.messages.len() equals `1`
   - Expected: req.messages[0].role equals `user`
   - Expected: req.messages[0].content equals `Hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct a prompt request with one user message")
step("Construct a production request from a prompt")
val req = new_chat_request_with_prompt("Hello world")
expect(req.messages.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(req.messages[0].role).to_equal("user")
expect(req.messages[0].content).to_equal("Hello world")
expect(req.temperature).to_be_less_than(0.0)
expect(req.stream).to_be(false)
```

</details>

#### should use exactly -1.0 as the unset-temperature marker

- should use exactly -1.0 as the unset-temperature marker
- Pin the sentinel value, not just its sign
   - Expected: req.temperature equals `-1.0`
   - Expected: new_chat_request_with_prompt("x").temperature equals `-1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should use exactly -1.0 as the unset-temperature marker")
step("Pin the sentinel value, not just its sign")
val req = new_chat_request()
expect(req.temperature).to_equal(-1.0)  # oracle: -1.0 — named expected value from the requirement
expect(new_chat_request_with_prompt("x").temperature).to_equal(-1.0)
```

</details>

#### should use exactly 0 as the unset-max_turns marker

- should use exactly 0 as the unset-max_turns marker
- Pin the sentinel value for turn limiting
   - Expected: new_chat_request().max_turns equals `0`
   - Expected: new_chat_request_with_prompt("x").max_turns equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should use exactly 0 as the unset-max_turns marker")
step("Pin the sentinel value for turn limiting")
expect(new_chat_request().max_turns).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(new_chat_request_with_prompt("x").max_turns).to_equal(0)
```

</details>

### ChatResponse

#### should construct every empty response default

- should construct every empty response default
- Construct a production empty response
   - Expected: resp.content equals ``
   - Expected: resp.model equals ``
   - Expected: resp.provider equals ``
   - Expected: resp.session_id equals ``
   - Expected: resp.stop_reason equals ``
   - Expected: resp.input_tokens equals `0`
   - Expected: resp.output_tokens equals `0`
   - Expected: resp.error equals ``
   - Expected: resp.raw equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct every empty response default")
step("Construct a production empty response")
val resp: ChatResponse = new_chat_response()
expect(resp.content).to_equal("")
expect(resp.model).to_equal("")
expect(resp.provider).to_equal("")
expect(resp.session_id).to_equal("")
expect(resp.stop_reason).to_equal("")
expect(resp.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(resp.output_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(resp.error).to_equal("")
expect(resp.is_error).to_be(false)
expect(resp.raw).to_equal("")
expect(response_ok(resp)).to_be(true)
expect(response_has_content(resp)).to_be(false)
```

</details>

#### should construct an error response and reject it

- should construct an error response and reject it
- Construct a production error response
   - Expected: resp.content equals ``
   - Expected: resp.stop_reason equals `error`
   - Expected: resp.error equals `Connection failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct an error response and reject it")
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

#### should construct a successful response with content

- should construct a successful response with content
- Construct a production successful response
   - Expected: resp.content equals `Hello!`
   - Expected: resp.stop_reason equals `end_turn`
   - Expected: resp.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct a successful response with content")
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

#### should treat empty successful content as absent

- should treat empty successful content as absent
- Construct a production successful response without content


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should treat empty successful content as absent")
step("Construct a production successful response without content")
val resp = new_success_response("")
expect(response_ok(resp)).to_be(true)
expect(response_has_content(resp)).to_be(false)
```

</details>

### StreamEvent

#### should construct a generic event with empty metadata

- should construct a generic event with empty metadata
- Construct a production generic stream event
   - Expected: evt.event_type equals `content_block_start`
   - Expected: evt.content equals `payload`
   - Expected: evt.session_id equals ``
   - Expected: evt.model equals ``
   - Expected: evt.stop_reason equals ``
   - Expected: evt.input_tokens equals `0`
   - Expected: evt.output_tokens equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct a generic event with empty metadata")
step("Construct a production generic stream event")
val evt: StreamEvent = new_stream_event("content_block_start", "payload")
expect(evt.event_type).to_equal("content_block_start")
expect(evt.content).to_equal("payload")
expect(evt.session_id).to_equal("")
expect(evt.model).to_equal("")
expect(evt.stop_reason).to_equal("")
expect(evt.input_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(evt.output_tokens).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should construct a text delta

- should construct a text delta
- Construct a production text-delta event
   - Expected: evt.event_type equals `text_delta`
   - Expected: evt.content equals `Hello `
   - Expected: evt.stop_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct a text delta")
step("Construct a production text-delta event")
val evt = new_text_delta("Hello ")
expect(evt.event_type).to_equal("text_delta")
expect(evt.content).to_equal("Hello ")
expect(evt.stop_reason).to_equal("")
```

</details>

#### should construct a message-stop event

- should construct a message-stop event
- Construct a production message-stop event
   - Expected: evt.event_type equals `message_stop`
   - Expected: evt.content equals ``
   - Expected: evt.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct a message-stop event")
step("Construct a production message-stop event")
val evt = new_message_stop("end_turn")
expect(evt.event_type).to_equal("message_stop")
expect(evt.content).to_equal("")
expect(evt.stop_reason).to_equal("end_turn")
```

</details>

### ProviderConfig

#### should construct every provider default

- should construct every provider default
- Construct a production provider configuration
   - Expected: cfg.provider_type equals `claude_cli`
   - Expected: cfg.base_url equals ``
   - Expected: cfg.api_key equals ``
   - Expected: cfg.model equals ``
   - Expected: cfg.cli_path equals ``
   - Expected: cfg.python_path equals ``
   - Expected: cfg.model_path equals ``
   - Expected: cfg.extra_args.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should construct every provider default")
step("Construct a production provider configuration")
val cfg: ProviderConfig = new_provider_config("claude_cli")
expect(cfg.provider_type).to_equal("claude_cli")
expect(cfg.base_url).to_equal("")
expect(cfg.api_key).to_equal("")
expect(cfg.model).to_equal("")
expect(cfg.cli_path).to_equal("")
expect(cfg.python_path).to_equal("")
expect(cfg.model_path).to_equal("")
expect(cfg.extra_args.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `c3e7123ed86988f53a48c679a22e65b63981b21a5e5a59306a5d7e9f4eb863fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3e7123ed86988f53a48c679a22e65b63981b21a5e5a59306a5d7e9f4eb863fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3e7123ed86988f53a48c679a22e65b63981b21a5e5a59306a5d7e9f4eb863fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/unit/app/llm_caret/types_spec.spl
mirror: doc/06_spec/unit/app/llm_caret/types_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_caret/types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_caret/types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_caret/types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/llm_caret/types_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve an explicit role and content' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/llm_caret/types_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve an explicit role and content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/types_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct and classify a user message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/llm_caret/types_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should construct and classify a user message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/types_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct and classify an assistant message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/llm_caret/types_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should construct and classify an assistant message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/types_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct and classify a system message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/llm_caret/types_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct every empty request default' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/llm_caret/types_spec.spl:101:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct a prompt request with one user message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
