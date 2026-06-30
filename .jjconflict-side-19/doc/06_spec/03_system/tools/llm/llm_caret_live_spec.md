# Llm Caret Live Specification

> <details>

<!-- sdn-diagram:id=llm_caret_live_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_caret_live_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_caret_live_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_caret_live_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Caret Live Specification

## Scenarios

### LLM Caret Live Integration

### Single-shot response

<details>
<summary>Advanced: returns non-empty response from claude CLI</summary>

#### returns non-empty response from claude CLI _(slow)_

1. print "  [DEBUG] content length: {resp content len
   - Expected: resp.is_error is false
   - Expected: resp.content.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude_simple("Reply with exactly: HELLO_SIMPLE")
print "  [DEBUG] is_error: {resp.is_error}"
print "  [DEBUG] error: {resp.error}"
print "  [DEBUG] content length: {resp.content.len()}"
print "  [DEBUG] content: {resp.content}"
expect(resp.is_error).to_equal(false)
expect(resp.content.len() > 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: response contains expected text for deterministic prompt</summary>

#### response contains expected text for deterministic prompt _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude_simple("What is 2 + 2? Reply with ONLY the number, nothing else.")
print "  [DEBUG] content: [{resp.content}]"
expect(resp.is_error).to_equal(false)
expect(resp.content.contains("4")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns model name in response</summary>

#### returns model name in response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude_simple("Say hi")
print "  [DEBUG] model: {resp.model}"
expect(resp.is_error).to_equal(false)
# Model field should be non-empty
expect(resp.model.len() > 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns session_id for conversation tracking</summary>

#### returns session_id for conversation tracking _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude_simple("Say hello")
print "  [DEBUG] session_id: {resp.session_id}"
expect(resp.is_error).to_equal(false)
expect(resp.session_id.len() > 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: reports token usage</summary>

#### reports token usage _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude_simple("Say ok")
print "  [DEBUG] input_tokens: {resp.input_tokens}"
print "  [DEBUG] output_tokens: {resp.output_tokens}"
expect(resp.is_error).to_equal(false)
# At least some tokens should be used
val total = resp.input_tokens + resp.output_tokens
expect(total > 0).to_equal(true)
```

</details>


</details>

### System prompt

<details>
<summary>Advanced: follows system prompt instructions</summary>

#### follows system prompt instructions _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude("What is your name?", "You are a helpful bot named BOTX99. Always include BOTX99 in your reply.", "", 1)
print "  [DEBUG] content: {resp.content}"
expect(resp.is_error).to_equal(false)
val upper = resp.content.upper()
expect(upper.contains("BOTX99")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: system prompt affects response style</summary>

#### system prompt affects response style _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude("Say hello", "You must reply in ALL CAPS only. No lowercase letters.", "", 1)
print "  [DEBUG] content: {resp.content}"
expect(resp.is_error).to_equal(false)
# Most of the response should be uppercase
val upper = resp.content.upper()
expect(upper.contains("HELLO")).to_equal(true)
```

</details>


</details>

### Multi-turn conversation

<details>
<summary>Advanced: maintains context across turns using session resume</summary>

#### maintains context across turns using session resume _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Turn 1: establish a fact
val resp1 = call_claude("Remember this secret code: ZEBRA42. Just say OK.", "", "", 1)
print "  [DEBUG] Turn 1 content: {resp1.content}"
print "  [DEBUG] Turn 1 session_id: {resp1.session_id}"
expect(resp1.is_error).to_equal(false)
expect(resp1.session_id.len() > 0).to_equal(true)

# Turn 2: ask about the fact using session resume
val sid = resp1.session_id
val resp2 = call_claude("What was the secret code I told you? Reply with ONLY the code.", "", sid, 1)
print "  [DEBUG] Turn 2 content: {resp2.content}"
expect(resp2.is_error).to_equal(false)
val upper2 = resp2.content.upper()
expect(upper2.contains("ZEBRA42")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: multi-turn with 3 exchanges</summary>

#### multi-turn with 3 exchanges _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Turn 1
val r1 = call_claude("I will give you 3 items. Item 1 is APPLE. Say OK.", "", "", 1)
print "  [DEBUG] T1: {r1.content}"
expect(r1.is_error).to_equal(false)
val sid1 = r1.session_id

# Turn 2
val r2 = call_claude("Item 2 is BANANA. Say OK.", "", sid1, 1)
print "  [DEBUG] T2: {r2.content}"
expect(r2.is_error).to_equal(false)

# Turn 3: recall
val r3 = call_claude("List all items I gave you, separated by commas.", "", sid1, 1)
print "  [DEBUG] T3: {r3.content}"
expect(r3.is_error).to_equal(false)
val upper3 = r3.content.upper()
expect(upper3.contains("APPLE")).to_equal(true)
expect(upper3.contains("BANANA")).to_equal(true)
```

</details>


</details>

### Response validation

<details>
<summary>Advanced: does not return ERROR prefix for valid requests</summary>

#### does not return ERROR prefix for valid requests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude_simple("Say hello world")
expect(resp.is_error).to_equal(false)
expect(resp.content.starts_with("ERROR")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: raw field contains original JSON</summary>

#### raw field contains original JSON _(slow)_

1. print "  [DEBUG] raw length: {resp raw len
   - Expected: resp.raw.len() > 0 is true
   - Expected: resp.raw contains `result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude_simple("Say hi")
print "  [DEBUG] raw length: {resp.raw.len()}"
expect(resp.raw.len() > 0).to_equal(true)
# Raw should contain JSON structure
expect(resp.raw.contains("result")).to_equal(true)
```

</details>


</details>

### Manual quality checks

<details>
<summary>Advanced: handles simple math question</summary>

#### handles simple math question _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude_simple("What is 15 * 7? Reply with ONLY the number.")
print "  [MANUAL CHECK] 15*7 = {resp.content}"
expect(resp.is_error).to_equal(false)
expect(resp.content.contains("105")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles text generation</summary>

#### handles text generation _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude_simple("Write exactly 3 words, nothing more.")
print "  [MANUAL CHECK] 3 words: [{resp.content}]"
expect(resp.is_error).to_equal(false)
expect(resp.content.len() > 0).to_equal(true)
# Should be reasonably short (3 words + maybe punctuation)
expect(resp.content.len() < 200).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles JSON-like structured response</summary>

#### handles JSON-like structured response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = call_claude("Return a JSON object with keys name and age. name=Alice age=30. Return ONLY the JSON, no markdown.", "You are a JSON generator. Return only valid JSON, no explanation, no markdown code fences.", "", 1)
print "  [MANUAL CHECK] JSON: {resp.content}"
expect(resp.is_error).to_equal(false)
expect(resp.content.contains("Alice")).to_equal(true)
expect(resp.content.contains("30")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/llm_caret_live_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM Caret Live Integration
- Single-shot response
- System prompt
- Multi-turn conversation
- Response validation
- Manual quality checks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 14 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
