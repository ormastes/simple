# chat_spec

> Purpose: Prove that production chat history.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# chat_spec

Purpose: Prove that production chat history.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/chat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that production chat history.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### production chat history

#### should start empty

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should start empty
- Verify: should start empty
   - Expected: length equals `0`
   - Expected: role equals ``
   - Expected: content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should start empty")
step("Verify: should start empty")
# @req: REQ-APP-LLM-CARET-001
_reset_chat_state()
val length = chat_history_len()
val role = chat_last_role()
val content = chat_last_content()
_reset_chat_state()
expect(length).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(role).to_equal("")
expect(content).to_equal("")
```

</details>

#### should add a user message

- should add a user message
- Verify: should add a user message
   - Expected: length equals `1`
   - Expected: role equals `user`
   - Expected: content equals `Hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should add a user message")
step("Verify: should add a user message")
_reset_chat_state()
chat_add_user("Hello")
val length = chat_history_len()
val role = chat_get_role(0)
val content = chat_get_content(0)
_reset_chat_state()
expect(length).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(role).to_equal("user")
expect(content).to_equal("Hello")
```

</details>

#### should add an assistant message

- should add an assistant message
- Verify: should add an assistant message
   - Expected: length equals `1`
   - Expected: role equals `assistant`
   - Expected: content equals `Hi there!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should add an assistant message")
step("Verify: should add an assistant message")
_reset_chat_state()
chat_add_assistant("Hi there!")
val length = chat_history_len()
val role = chat_get_role(0)
val content = chat_get_content(0)
_reset_chat_state()
expect(length).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(role).to_equal("assistant")
expect(content).to_equal("Hi there!")
```

</details>

#### should preserve custom roles through the generic message API

- should preserve custom roles through the generic message API
- Verify: should preserve custom roles through the generic message API
   - Expected: role equals `tool`
   - Expected: content equals `tool fixture`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should preserve custom roles through the generic message API")
step("Verify: should preserve custom roles through the generic message API")
_reset_chat_state()
chat_add_message("tool", "tool fixture")
val role = chat_get_role(0)
val content = chat_get_content(0)
_reset_chat_state()
expect(role).to_equal("tool")
expect(content).to_equal("tool fixture")
```

</details>

#### should maintain conversation order

- should maintain conversation order
- Verify: should maintain conversation order
   - Expected: length equals `3`
   - Expected: first equals `user`
   - Expected: second equals `assistant`
   - Expected: third equals `user`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should maintain conversation order")
step("Verify: should maintain conversation order")
_reset_chat_state()
chat_add_user("Hi")
chat_add_assistant("Hello!")
chat_add_user("How are you?")
val length = chat_history_len()
val first = chat_get_role(0)
val second = chat_get_role(1)
val third = chat_get_role(2)
_reset_chat_state()
expect(length).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(first).to_equal("user")
expect(second).to_equal("assistant")
expect(third).to_equal("user")
```

</details>

#### should clear populated history

- should clear populated history
- Verify: should clear populated history
   - Expected: length equals `0`
   - Expected: content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should clear populated history")
step("Verify: should clear populated history")
_reset_chat_state()
chat_add_user("test")
chat_clear()
val length = chat_history_len()
val content = chat_last_content()
_reset_chat_state()
expect(length).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(content).to_equal("")
```

</details>

#### should return empty text for every out-of-bounds lookup

- should return empty text for every out-of-bounds lookup
- Verify: should return empty text for every out-of-bounds lookup
   - Expected: negative_role equals ``
   - Expected: high_role equals ``
   - Expected: negative_content equals ``
   - Expected: high_content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should return empty text for every out-of-bounds lookup")
step("Verify: should return empty text for every out-of-bounds lookup")
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

#### should return the last role and content

- should return the last role and content
- Verify: should return the last role and content
   - Expected: role equals `assistant`
   - Expected: content equals `Second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should return the last role and content")
step("Verify: should return the last role and content")
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

### production chat truncation

#### should retain only the last requested messages

- should retain only the last requested messages
- Verify: should retain only the last requested messages
   - Expected: length equals `2`
   - Expected: first equals `msg2`
   - Expected: second equals `resp2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should retain only the last requested messages")
step("Verify: should retain only the last requested messages")
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
expect(length).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(first).to_equal("msg2")
expect(second).to_equal("resp2")
```

</details>

#### should leave history unchanged when the limit exceeds its length

- should leave history unchanged when the limit exceeds its length
- Verify: should leave history unchanged when the limit exceeds its length
   - Expected: length equals `1`
   - Expected: content equals `msg1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should leave history unchanged when the limit exceeds its length")
step("Verify: should leave history unchanged when the limit exceeds its length")
_reset_chat_state()
chat_add_user("msg1")
chat_truncate(10)
val length = chat_history_len()
val content = chat_get_content(0)
_reset_chat_state()
expect(length).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(content).to_equal("msg1")
```

</details>

#### should clear history when truncating to zero

- should clear history when truncating to zero
- Verify: should clear history when truncating to zero
   - Expected: length equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should clear history when truncating to zero")
step("Verify: should clear history when truncating to zero")
_reset_chat_state()
chat_add_user("msg1")
chat_add_assistant("resp1")
chat_truncate(0)
val length = chat_history_len()
_reset_chat_state()
expect(length).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should auto-truncate after exceeding maximum history

- should auto-truncate after exceeding maximum history
- Verify: should auto-truncate after exceeding maximum history
   - Expected: length equals `3`
   - Expected: first equals `b`
   - Expected: last equals `d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should auto-truncate after exceeding maximum history")
step("Verify: should auto-truncate after exceeding maximum history")
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
expect(length).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(first).to_equal("b")
expect(last).to_equal("d")
```

</details>

### production chat system prompt

#### should set and read the system prompt

- should set and read the system prompt
- Verify: should set and read the system prompt
   - Expected: prompt equals `Be helpful`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should set and read the system prompt")
step("Verify: should set and read the system prompt")
_reset_chat_state()
chat_set_system_prompt("Be helpful")
val prompt = chat_get_system_prompt()
_reset_chat_state()
expect(prompt).to_equal("Be helpful")
```

</details>

#### should clear the system prompt

- should clear the system prompt
- Verify: should clear the system prompt
   - Expected: prompt equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should clear the system prompt")
step("Verify: should clear the system prompt")
_reset_chat_state()
chat_set_system_prompt("temporary")
chat_set_system_prompt("")
val prompt = chat_get_system_prompt()
_reset_chat_state()
expect(prompt).to_equal("")
```

</details>

### production chat JSON

#### should build an empty messages array

- should build an empty messages array
- Verify: should build an empty messages array
   - Expected: json equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should build an empty messages array")
step("Verify: should build an empty messages array")
_reset_chat_state()
val json = chat_build_messages_json()
_reset_chat_state()
expect(json).to_equal("[]")
```

</details>

#### should build ordered role and content objects

- should build ordered role and content objects
- Verify: should build ordered role and content objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should build ordered role and content objects")
step("Verify: should build ordered role and content objects")
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

#### should escape quotes slashes and control characters

- should escape quotes slashes and control characters
- Verify: should escape quotes slashes and control characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should escape quotes slashes and control characters")
step("Verify: should escape quotes slashes and control characters")
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

### production tool result presentation

#### should derive success and error statuses

- should derive success and error statuses
- Verify: should derive success and error statuses
   - Expected: tool_call_status(ok) equals `ok`
   - Expected: tool_call_status(failed) equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should derive success and error statuses")
step("Verify: should derive success and error statuses")
val ok = new_tool_result("call-ok", "done")
val failed = new_tool_error("call-failed", "failed")
expect(tool_call_status(ok)).to_equal("ok")
expect(tool_call_status(failed)).to_equal("error")
```

</details>

#### should redact secrets from summaries

- should redact secrets from summaries
- Verify: should redact secrets from summaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should redact secrets from summaries")
step("Verify: should redact secrets from summaries")
val secret = "sk-ant-api03-ABCDEFGHIJ1234"
val summary = tool_call_summary(
    new_tool_error("call-secret", "failed " + secret)
)
expect(summary).to_contain("failed")
expect(summary.contains(secret)).to_be(false)
```

</details>

#### should cap summaries at two hundred visible characters

- should cap summaries at two hundred visible characters
- Verify: should cap summaries at two hundred visible characters
   - Expected: summary.len() equals `203`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should cap summaries at two hundred visible characters")
step("Verify: should cap summaries at two hundred visible characters")
var content = "xxxxxxxxxx"
while content.len() < 240:
    content = content + content
val summary = tool_call_summary(
    new_tool_result("call-long", content)
)
expect(summary.len()).to_equal(203)  # oracle: 203 — named expected value from the requirement
expect(summary).to_end_with("...")
```

</details>

#### should wrap redacted tool results as untrusted transcript input

- should wrap redacted tool results as untrusted transcript input
- Verify: should wrap redacted tool results as untrusted transcript input


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should wrap redacted tool results as untrusted transcript input")
step("Verify: should wrap redacted tool results as untrusted transcript input")
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

### production agent loop

#### should finish a text-only response in one iteration

- should finish a text-only response in one iteration
- Verify: should finish a text-only response in one iteration
   - Expected: result.final_text equals `final fixture`
   - Expected: result.iterations equals `1`
   - Expected: result.stopped_reason equals `end_turn`
   - Expected: result.tool_calls_made equals `0`
   - Expected: result.final_transcript.len() equals `2`
   - Expected: result.final_transcript[1].role equals `assistant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should finish a text-only response in one iteration")
step("Verify: should finish a text-only response in one iteration")
_reset_chat_test_seams()
val result = run_agent_loop(
    default_policy("build/tmp/llm_caret_chat_test"),
    [Message(role: "user", content: "fixture")],
    _text_responder,
    3
)
_reset_chat_test_seams()
expect(result.final_text).to_equal("final fixture")
expect(result.iterations).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result.stopped_reason).to_equal("end_turn")
expect(result.tool_calls_made).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.final_transcript.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(result.final_transcript[1].role).to_equal("assistant")
```

</details>

#### should gate an unknown tool and render its error before continuing

- should gate an unknown tool and render its error before continuing
- Verify: should gate an unknown tool and render its error before continuing
   - Expected: result.final_text equals `finished fixture`
   - Expected: result.iterations equals `2`
   - Expected: result.stopped_reason equals `end_turn`
   - Expected: result.tool_calls_made equals `1`
   - Expected: result.final_transcript.len() equals `4`
   - Expected: result.final_transcript[1].role equals `assistant`
   - Expected: result.final_transcript[2].role equals `user`
   - Expected: result.final_transcript[3].role equals `assistant`
   - Expected: render_calls equals `1`
   - Expected: render_name equals `unknown_fixture_tool`
   - Expected: render_status equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should gate an unknown tool and render its error before continuing")
step("Verify: should gate an unknown tool and render its error before continuing")
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
expect(result.iterations).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(result.stopped_reason).to_equal("end_turn")
expect(result.tool_calls_made).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result.final_transcript.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(result.final_transcript[1].role).to_equal("assistant")
expect(result.final_transcript[2].role).to_equal("user")
expect(result.final_transcript[2].content).to_contain("tool_result")
expect(result.final_transcript[3].role).to_equal("assistant")
expect(render_calls).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(render_name).to_equal("unknown_fixture_tool")
expect(render_status).to_equal("error")
expect(render_summary).to_contain("unknown tool")
```

</details>

<details>
<summary>Advanced: should stop a repeated tool loop at the requested cap</summary>

#### should stop a repeated tool loop at the requested cap

- should stop a repeated tool loop at the requested cap
- Verify: should stop a repeated tool loop at the requested cap
   - Expected: result.final_text equals `waiting fixture`
   - Expected: result.iterations equals `2`
   - Expected: result.stopped_reason equals `max_iterations`
   - Expected: result.tool_calls_made equals `2`
   - Expected: result.final_transcript.len() equals `5`
   - Expected: render_calls equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should stop a repeated tool loop at the requested cap")
step("Verify: should stop a repeated tool loop at the requested cap")
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
expect(result.iterations).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(result.stopped_reason).to_equal("max_iterations")
expect(result.tool_calls_made).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(result.final_transcript.len()).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(render_calls).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `59f0645e278dffd57f6285dfb1774c4a6585ff413cc3697ae0ed41657cca0da7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59f0645e278dffd57f6285dfb1774c4a6585ff413cc3697ae0ed41657cca0da7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59f0645e278dffd57f6285dfb1774c4a6585ff413cc3697ae0ed41657cca0da7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/llm_caret/chat_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/chat_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/chat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/chat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/chat_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should start empty' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/chat_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should start empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/chat_spec.spl:101:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should add a user message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/chat_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should add a user message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/chat_spec.spl:115:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should add an assistant message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/chat_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should add an assistant message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/chat_spec.spl:129:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve custom roles through the generic message API' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/chat_spec.spl:141:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should maintain conversation order' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/chat_spec.spl:159:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clear populated history' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
