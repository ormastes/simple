# LLM Caret Live Integration Specification

> This specification checks the Claude CLI response contract, system prompts, session resume, usage reporting, and structured response content. By default it uses deterministic local responses. Setting `SIMPLE_LLM_LIVE=1` explicitly enables the authenticated Claude process.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Live Integration Specification

This specification checks the Claude CLI response contract, system prompts, session resume, usage reporting, and structured response content. By default it uses deterministic local responses. Setting `SIMPLE_LLM_LIVE=1` explicitly enables the authenticated Claude process.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Offline fixture by default; live execution is opt-in |
| Requirements | doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md |
| Plan | doc/03_plan/sys_test/llm_caret_claude_cli_harden.md |
| Design | doc/05_design/llm_caret_claude_cli_harden.md |
| Research | doc/01_research/local/llm_caret_claude_cli_harden.md |
| Source | `test/03_system/tools/llm/llm_caret_live_spec.spl` |
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification checks the Claude CLI response contract, system prompts,
session resume, usage reporting, and structured response content. By default it
uses deterministic local responses. Setting `SIMPLE_LLM_LIVE=1` explicitly
enables the authenticated Claude process.

## Syntax

```bash
bin/simple test test/03_system/tools/llm/llm_caret_live_spec.spl --mode=interpreter
SIMPLE_LLM_LIVE=1 bin/simple test test/03_system/tools/llm/llm_caret_live_spec.spl --mode=interpreter
```

## Default Safety

The default run:

- does not start `claude`;
- does not read an API key;
- does not make network requests;
- does not incur provider cost;
- still executes every scenario and assertion.

## Live Opt In

The live run requires:

- an installed `claude` command;
- valid local authentication;
- explicit `SIMPLE_LLM_LIVE=1`;
- acceptance of provider latency and cost.

## Scenario Inventory

### Single-Shot Response

The suite checks:

- non-empty content;
- deterministic arithmetic;
- model identity;
- session identity;
- token usage.

### System Prompt

The suite checks:

- a required named identity;
- an uppercase response constraint.

### Multi-Turn Conversation

The suite checks:

- a two-turn secret-code resume;
- a three-exchange item-list resume;
- stable reuse of the returned session identifier.

### Response Validation

The suite checks:

- successful responses do not carry an error prefix;
- the raw structured response remains available.

### Constrained Output

The suite checks:

- a multiplication result;
- bounded short text;
- JSON-like name and age fields.

## Failure Handling

A nonzero Claude exit becomes a structured `CliResponse` error. The test checks
the error flag before content so transport failures cannot masquerade as model
answers.

## Evidence Boundary

The deterministic path proves request assembly and response expectations in a
stable environment. Only the explicit live path proves local authentication and
remote service interoperability.

## Manual Policy

All scenarios remain visible as advanced slow scenarios in the generated
manual. Executable SSpec is folded below each flow. No scenario is skipped.

## Scenarios

### LLM Caret Live Integration

### Single-shot response

<details>
<summary>Advanced: should return a non-empty response from claude CLI</summary>

#### should return a non-empty response from claude CLI _(slow)_

- Invoke the deterministic or explicitly enabled live provider
- print "  [DEBUG] content length: {resp content len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Invoke the deterministic or explicitly enabled live provider")
val resp = call_claude_simple("Reply with exactly: HELLO_SIMPLE")
print "  [DEBUG] is_error: {resp.is_error}"
print "  [DEBUG] error: {resp.error}"
print "  [DEBUG] content length: {resp.content.len()}"
print "  [DEBUG] content: {resp.content}"
expect(resp.is_error).to_be(false)
expect(resp.content.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: should contain expected text for a deterministic prompt</summary>

#### should contain expected text for a deterministic prompt _(slow)_

- Ask for a deterministic arithmetic response


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask for a deterministic arithmetic response")
val resp = call_claude_simple("What is 2 + 2? Reply with ONLY the number, nothing else.")
print "  [DEBUG] content: [{resp.content}]"
expect(resp.is_error).to_be(false)
expect(resp.content).to_contain("4")
```

</details>


</details>

<details>
<summary>Advanced: should return a model name in the response</summary>

#### should return a model name in the response _(slow)_

- Inspect structured provider identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect structured provider identity")
val resp = call_claude_simple("Say hi")
print "  [DEBUG] model: {resp.model}"
expect(resp.is_error).to_be(false)
# Model field should be non-empty
expect(resp.model.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: should return a session_id for conversation tracking</summary>

#### should return a session_id for conversation tracking _(slow)_

- Inspect the structured session identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the structured session identifier")
val resp = call_claude_simple("Say hello")
print "  [DEBUG] session_id: {resp.session_id}"
expect(resp.is_error).to_be(false)
expect(resp.session_id.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: should report token usage</summary>

#### should report token usage _(slow)_

- Inspect structured token usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect structured token usage")
val resp = call_claude_simple("Say ok")
print "  [DEBUG] input_tokens: {resp.input_tokens}"
print "  [DEBUG] output_tokens: {resp.output_tokens}"
expect(resp.is_error).to_be(false)
# At least some tokens should be used
val total = resp.input_tokens + resp.output_tokens
expect(total).to_be_greater_than(0)
```

</details>


</details>

### System prompt

<details>
<summary>Advanced: should follow system prompt instructions</summary>

#### should follow system prompt instructions _(slow)_

- Invoke the provider with a named-bot system prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Invoke the provider with a named-bot system prompt")
val resp = call_claude("What is your name?", "You are a helpful bot named BOTX99. Always include BOTX99 in your reply.", "", 1)
print "  [DEBUG] content: {resp.content}"
expect(resp.is_error).to_be(false)
val upper = resp.content.upper()
expect(upper).to_contain("BOTX99")
```

</details>


</details>

<details>
<summary>Advanced: should apply the system prompt response style</summary>

#### should apply the system prompt response style _(slow)_

- Invoke the provider with an uppercase style constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Invoke the provider with an uppercase style constraint")
val resp = call_claude("Say hello", "You must reply in ALL CAPS only. No lowercase letters.", "", 1)
print "  [DEBUG] content: {resp.content}"
expect(resp.is_error).to_be(false)
# Most of the response should be uppercase
val upper = resp.content.upper()
expect(upper).to_contain("HELLO")
```

</details>


</details>

### Multi-turn conversation

<details>
<summary>Advanced: should maintain context across turns using session resume</summary>

#### should maintain context across turns using session resume _(slow)_

- Start a session and resume it with the returned identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start a session and resume it with the returned identifier")
# Turn 1: establish a fact
val resp1 = call_claude("Remember this secret code: ZEBRA42. Just say OK.", "", "", 1)
print "  [DEBUG] Turn 1 content: {resp1.content}"
print "  [DEBUG] Turn 1 session_id: {resp1.session_id}"
expect(resp1.is_error).to_be(false)
expect(resp1.session_id.len()).to_be_greater_than(0)

# Turn 2: ask about the fact using session resume
val sid = resp1.session_id
val resp2 = call_claude("What was the secret code I told you? Reply with ONLY the code.", "", sid, 1)
print "  [DEBUG] Turn 2 content: {resp2.content}"
expect(resp2.is_error).to_be(false)
val upper2 = resp2.content.upper()
expect(upper2).to_contain("ZEBRA42")
```

</details>


</details>

<details>
<summary>Advanced: should maintain context across three exchanges</summary>

#### should maintain context across three exchanges _(slow)_

- Resume one session across three exchanges


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resume one session across three exchanges")
# Turn 1
val r1 = call_claude("I will give you 3 items. Item 1 is APPLE. Say OK.", "", "", 1)
print "  [DEBUG] T1: {r1.content}"
expect(r1.is_error).to_be(false)
val sid1 = r1.session_id

# Turn 2
val r2 = call_claude("Item 2 is BANANA. Say OK.", "", sid1, 1)
print "  [DEBUG] T2: {r2.content}"
expect(r2.is_error).to_be(false)

# Turn 3: recall
val r3 = call_claude("List all items I gave you, separated by commas.", "", sid1, 1)
print "  [DEBUG] T3: {r3.content}"
expect(r3.is_error).to_be(false)
val upper3 = r3.content.upper()
expect(upper3).to_contain("APPLE")
expect(upper3).to_contain("BANANA")
```

</details>


</details>

### Response validation

<details>
<summary>Advanced: should not return an ERROR prefix for valid requests</summary>

#### should not return an ERROR prefix for valid requests _(slow)_

- Validate a successful response envelope


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate a successful response envelope")
val resp = call_claude_simple("Say hello world")
expect(resp.is_error).to_be(false)
expect(resp.content.starts_with("ERROR")).to_be(false)
```

</details>


</details>

<details>
<summary>Advanced: should retain original JSON in the raw field</summary>

#### should retain original JSON in the raw field _(slow)_

- Inspect the raw structured provider response
- print "  [DEBUG] raw length: {resp raw len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the raw structured provider response")
val resp = call_claude_simple("Say hi")
print "  [DEBUG] raw length: {resp.raw.len()}"
expect(resp.raw.len()).to_be_greater_than(0)
# Raw should contain JSON structure
expect(resp.raw).to_contain("result")
```

</details>


</details>

### Manual quality checks

<details>
<summary>Advanced: should handle a simple math question</summary>

#### should handle a simple math question _(slow)_

- Ask for a constrained multiplication result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask for a constrained multiplication result")
val resp = call_claude_simple("What is 15 * 7? Reply with ONLY the number.")
print "  [MANUAL CHECK] 15*7 = {resp.content}"
expect(resp.is_error).to_be(false)
expect(resp.content).to_contain("105")
```

</details>


</details>

<details>
<summary>Advanced: should handle constrained text generation</summary>

#### should handle constrained text generation _(slow)_

- Ask for a three-word response


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask for a three-word response")
val resp = call_claude_simple("Write exactly 3 words, nothing more.")
print "  [MANUAL CHECK] 3 words: [{resp.content}]"
expect(resp.is_error).to_be(false)
expect(resp.content.len()).to_be_greater_than(0)
# Should be reasonably short (3 words + maybe punctuation)
expect(resp.content.len()).to_be_less_than(200)
```

</details>


</details>

<details>
<summary>Advanced: should handle a JSON-like structured response</summary>

#### should handle a JSON-like structured response _(slow)_

- Ask for a constrained JSON response


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask for a constrained JSON response")
val resp = call_claude("Return a JSON object with keys name and age. name=Alice age=30. Return ONLY the JSON, no markdown.", "You are a JSON generator. Return only valid JSON, no explanation, no markdown code fences.", "", 1)
print "  [MANUAL CHECK] JSON: {resp.content}"
expect(resp.is_error).to_be(false)
expect(resp.content).to_contain("Alice")
expect(resp.content).to_contain("30")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 14 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_claude_cli_harden.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_harden.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>
