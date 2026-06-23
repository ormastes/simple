# Llm Caret Live Comprehensive Specification

> <details>

<!-- sdn-diagram:id=llm_caret_live_comprehensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_caret_live_comprehensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_caret_live_comprehensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_caret_live_comprehensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Caret Live Comprehensive Specification

## Scenarios

### LLM Caret Live Comprehensive Integration

### Section 1: Single-shot responses

<details>
<summary>Advanced: returns exact text in response</summary>

#### returns exact text in response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = call_claude_simple("Reply with exactly: HELLO_SIMPLE")
val stdout = result.0 ?? ""
val exit_code = result.2

expect(exit_code).to_equal(0)

val content = _extract_json_string(stdout, "result")
print "  [MANUAL] Content: {content}"
expect(content.contains("HELLO_SIMPLE")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles simple math</summary>

#### handles simple math _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = call_claude_simple("What is 2 + 2? Reply with ONLY the number.")
val stdout = result.0 ?? ""
val content = _extract_json_string(stdout, "result")

print "  [MANUAL] Math result: {content}"
expect(content.contains("4")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns model name</summary>

#### returns model name _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = call_claude_simple("Say hi")
val stdout = result.0 ?? ""
val model = _extract_json_string(stdout, "model")
val content = _extract_json_string(stdout, "result")
val session_id = _extract_json_string(stdout, "session_id")

print "  [MANUAL] Model: {model}"
val has_identity = model.len() > 0 or content.len() > 0 or session_id.len() > 0
expect(has_identity).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns session_id for tracking</summary>

#### returns session_id for tracking _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = call_claude_simple("Say hello")
val stdout = result.0 ?? ""
val session_id = _extract_json_string(stdout, "session_id")

print "  [MANUAL] Session ID: {session_id}"
expect(session_id.len() > 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: reports token usage</summary>

#### reports token usage _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = call_claude_simple("Say ok")
val stdout = result.0 ?? ""
val in_tok = _extract_json_int(stdout, "input_tokens")
val out_tok = _extract_json_int(stdout, "output_tokens")
val total = in_tok + out_tok

print "  [MANUAL] Tokens: in={in_tok}, out={out_tok}, total={total}"
expect(total > 0).to_equal(true)
```

</details>


</details>

### Section 2: System prompt adherence

<details>
<summary>Advanced: follows pirate persona system prompt</summary>

#### follows pirate persona system prompt _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = call_claude(
    "What are you?",
    "You are a pirate named CaptainBytes. Always speak in pirate dialect. Every response MUST include 'Arrr!'",
    "",
    1
)
val stdout = result.0 ?? ""
val content = _extract_json_string(stdout, "result")
val lower = content.lower()

print "  [MANUAL] Pirate response: {content}"
expect(lower.contains("arr")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: follows CSV format constraint</summary>

#### follows CSV format constraint _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = call_claude(
    "List 3 fruits",
    "You MUST respond in CSV format only. No explanations, just comma-separated values on a single line.",
    "",
    1
)
val stdout = result.0 ?? ""
val content = _extract_json_string(stdout, "result")

print "  [MANUAL] CSV response: {content}"
expect(content.contains(",")).to_equal(true)
```

</details>


</details>

### Section 3: Multi-turn conversation (6 turns)

<details>
<summary>Advanced: maintains context across 6 turns with session resume</summary>

#### maintains context across 6 turns with session resume _(slow)_

1.  skip long live


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_skip_long_live("6-turn context resume")
```

</details>


</details>

### Section 4: Code tutor session (5 turns)

<details>
<summary>Advanced: progressive code Q&A with context building</summary>

#### progressive code Q&A with context building _(slow)_

1.  skip long live


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_skip_long_live("code tutor session")
```

</details>


</details>

### Section 5: Shopping list state tracking (5 turns)

<details>
<summary>Advanced: maintains mutable state across conversation</summary>

#### maintains mutable state across conversation _(slow)_

1.  skip long live


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_skip_long_live("shopping list state tracking")
```

</details>


</details>

### Section 6: Edge cases

<details>
<summary>Advanced: handles repetition requests</summary>

#### handles repetition requests _(slow)_

1. idx = idx + found idx + search len
   - Expected: upper contains `PLATYPUS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = call_claude_simple("Repeat PLATYPUS exactly 5 times separated by spaces. Nothing else.")
val stdout = result.0 ?? ""
val content = _extract_json_string(stdout, "result")
val upper = content.upper()

# Count occurrences manually
var count = 0
var idx = 0
val search = "PLATYPUS"
while idx < upper.len():
    val found_idx = _unwrap_idx(upper.substring(idx).index_of(search))
    if found_idx >= 0:
        count = count + 1
        idx = idx + found_idx + search.len()
    else:
        break

print "  [EDGE] Repetition count: {count}, content: {content}"
expect(upper.contains("PLATYPUS")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles exact phrase requests</summary>

#### handles exact phrase requests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = call_claude_simple("Reply with exactly: hello world test")
val stdout = result.0 ?? ""
val content = _extract_json_string(stdout, "result")
val lower = content.lower()

print "  [EDGE] Exact phrase: {content}"
expect(lower.contains("hello")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/llm_caret_live_comprehensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM Caret Live Comprehensive Integration
- Section 1: Single-shot responses
- Section 2: System prompt adherence
- Section 3: Multi-turn conversation (6 turns)
- Section 4: Code tutor session (5 turns)
- Section 5: Shopping list state tracking (5 turns)
- Section 6: Edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 12 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
