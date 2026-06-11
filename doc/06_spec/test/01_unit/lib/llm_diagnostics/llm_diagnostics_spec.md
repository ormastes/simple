# Llm Diagnostics Specification

> <details>

<!-- sdn-diagram:id=llm_diagnostics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_diagnostics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_diagnostics_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_diagnostics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Diagnostics Specification

## Scenarios

### LLM Diagnostics

### types

#### creates default token usage with zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = new_token_usage()
expect(u.input_tokens).to_equal(0)
expect(u.output_tokens).to_equal(0)
expect(u.cache_read_input_tokens).to_equal(0)
expect(u.cache_creation_input_tokens).to_equal(0)
```

</details>

#### computes total input tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = TokenUsage(
    input_tokens: 100,
    output_tokens: 50,
    cache_read_input_tokens: 200,
    cache_creation_input_tokens: 50
)
expect(token_usage_total_input(u)).to_equal(350)
expect(token_usage_total(u)).to_equal(400)
```

</details>

#### adds token usages

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = TokenUsage(input_tokens: 10, output_tokens: 5, cache_read_input_tokens: 20, cache_creation_input_tokens: 3)
val b = TokenUsage(input_tokens: 30, output_tokens: 15, cache_read_input_tokens: 40, cache_creation_input_tokens: 7)
val sum = token_usage_add(a, b)
expect(sum.input_tokens).to_equal(40)
expect(sum.output_tokens).to_equal(20)
expect(sum.cache_read_input_tokens).to_equal(60)
expect(sum.cache_creation_input_tokens).to_equal(10)
```

</details>

#### computes tool call latency

1. var tc = new tool call
   - Expected: tool_call_latency_ms(tc) equals `250`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tc = new_tool_call("id1", "Bash")
tc.start_time = 1000
tc.end_time = 1250
expect(tool_call_latency_ms(tc)).to_equal(250)
```

</details>

#### creates config with log path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = diag_config_with_log("/tmp/diag.jsonl")
expect(cfg.log_path).to_equal("/tmp/diag.jsonl")
expect(cfg.capture_content).to_equal(false)
```

</details>

#### creates config with content capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = diag_config_with_content("/tmp/diag.jsonl")
expect(cfg.capture_content).to_equal(true)
```

</details>

### token_estimator

#### estimates tokens from content length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(estimate_tokens("hello world!!", 4.0)).to_equal(3)
```

</details>

#### returns 0 for empty content

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(estimate_tokens_default("")).to_equal(0)
```

</details>

#### estimates JSON tokens with lower ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":\"value\"}"
val tokens = estimate_json_tokens(json)
expect(tokens).to_be_greater_than(0)
```

</details>

#### truncates content to max size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val long = "abcdefghijklmnopqrstuvwxyz"
val short = truncate_content(long, 5)
expect(short.len()).to_equal(5)
```

</details>

#### does not truncate short content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short = "abc"
expect(truncate_content(short, 10)).to_equal("abc")
```

</details>

### hook_handler

#### parses MCP tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_mcp_tool_name("mcp__simple-mcp__simple_build")
expect(parsed.0).to_equal("simple-mcp")
expect(parsed.1).to_equal("simple_build")
```

</details>

#### returns empty server for non-MCP tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_mcp_tool_name("Bash")
expect(parsed.0).to_equal("")
expect(parsed.1).to_equal("Bash")
```

</details>

#### detects MCP tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_mcp_tool("mcp__server__tool")).to_equal(true)
expect(is_mcp_tool("Bash")).to_equal(false)
```

</details>

#### extracts string from JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\":\"test\",\"value\":\"hello\"}"
expect(extract_str(json, "name")).to_equal("test")
expect(extract_str(json, "value")).to_equal("hello")
expect(extract_str(json, "missing")).to_equal("")
```

</details>

#### extracts int from JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"count\":42,\"size\":100}"
expect(extract_int(json, "count")).to_equal(42)
expect(extract_int(json, "size")).to_equal(100)
expect(extract_int(json, "missing")).to_equal(0)
```

</details>

#### maps hook event names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(map_event_name("PreToolUse")).to_equal(EVENT_TOOL_PRE)
expect(map_event_name("PostToolUse")).to_equal(EVENT_TOOL_POST)
expect(map_event_name("SessionStart")).to_equal(EVENT_SESSION_START)
```

</details>

#### parses hook JSON into DiagEvent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"hook_event_name\":\"PreToolUse\",\"session_id\":\"abc123\",\"tool_name\":\"Bash\"}"
val event = parse_hook_json(json)
expect(event.event_type).to_equal(EVENT_TOOL_PRE)
expect(event.session_id).to_equal("abc123")
```

</details>

### cache_analyzer

#### analyzes cache hits across turns

1. TokenUsage
2. TokenUsage
3. TokenUsage
   - Expected: analysis.total_cache_reads equals `300`
   - Expected: analysis.total_cache_writes equals `200`
   - Expected: analysis.total_uncached equals `200`
   - Expected: analysis.per_turn.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val turns = [
    TokenUsage(input_tokens: 100, output_tokens: 50, cache_read_input_tokens: 0, cache_creation_input_tokens: 200),
    TokenUsage(input_tokens: 50, output_tokens: 30, cache_read_input_tokens: 150, cache_creation_input_tokens: 0),
    TokenUsage(input_tokens: 50, output_tokens: 40, cache_read_input_tokens: 150, cache_creation_input_tokens: 0)
]
val analysis = analyze_cache(turns)
expect(analysis.total_cache_reads).to_equal(300)
expect(analysis.total_cache_writes).to_equal(200)
expect(analysis.total_uncached).to_equal(200)
expect(analysis.per_turn.len()).to_equal(3)
```

</details>

#### detects first cache hit turn

1. TokenUsage
2. TokenUsage
   - Expected: first_cache_hit_turn(analysis) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val turns = [
    TokenUsage(input_tokens: 100, output_tokens: 50, cache_read_input_tokens: 0, cache_creation_input_tokens: 200),
    TokenUsage(input_tokens: 50, output_tokens: 30, cache_read_input_tokens: 150, cache_creation_input_tokens: 0)
]
val analysis = analyze_cache(turns)
expect(first_cache_hit_turn(analysis)).to_equal(1)
```

</details>

#### returns -1 when no cache hits

1. TokenUsage
   - Expected: first_cache_hit_turn(analysis) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val turns = [
    TokenUsage(input_tokens: 100, output_tokens: 50, cache_read_input_tokens: 0, cache_creation_input_tokens: 0)
]
val analysis = analyze_cache(turns)
expect(first_cache_hit_turn(analysis)).to_equal(-1)
```

</details>

### collector

#### initializes and tracks state

1. diag init
   - Expected: diag_is_initialized() is true
   - Expected: diag_get_event_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = diag_config_with_log("/tmp/test.jsonl")
diag_init(cfg)
expect(diag_is_initialized()).to_equal(true)
expect(diag_get_event_count()).to_equal(0)
```

</details>

#### buffers events

1. diag init
2. var event = new diag event
3. diag push event
   - Expected: diag_get_event_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = diag_config_with_log("/tmp/test.jsonl")
diag_init(cfg)
var event = new_diag_event(EVENT_SESSION_START, "test-session")
event.timestamp = 1000
diag_push_event(event)
expect(diag_get_event_count()).to_equal(1)
```

</details>

#### resets state

1. diag init
2. var event = new diag event
3. diag push event
4. diag reset
   - Expected: diag_get_event_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = diag_config_with_log("/tmp/test.jsonl")
diag_init(cfg)
var event = new_diag_event(EVENT_SESSION_START, "s1")
event.timestamp = 1000
diag_push_event(event)
diag_reset()
expect(diag_get_event_count()).to_equal(0)
```

</details>

### timeline

#### sorts events by timestamp

1. var e1 = new diag event
2. var e2 = new diag event
3. var e3 = new diag event
   - Expected: sorted[0].timestamp equals `100`
   - Expected: sorted[1].timestamp equals `200`
   - Expected: sorted[2].timestamp equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e1 = new_diag_event("a", "s1")
e1.timestamp = 300
var e2 = new_diag_event("b", "s1")
e2.timestamp = 100
var e3 = new_diag_event("c", "s1")
e3.timestamp = 200
val sorted = sort_events_by_time([e1, e2, e3])
expect(sorted[0].timestamp).to_equal(100)
expect(sorted[1].timestamp).to_equal(200)
expect(sorted[2].timestamp).to_equal(300)
```

</details>

#### filters by event type

1. var e1 = new diag event
2. var e2 = new diag event
3. var e3 = new diag event
   - Expected: filtered.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e1 = new_diag_event(EVENT_TOOL_PRE, "s1")
var e2 = new_diag_event(EVENT_SESSION_START, "s1")
var e3 = new_diag_event(EVENT_TOOL_PRE, "s1")
val filtered = filter_events_by_type([e1, e2, e3], EVENT_TOOL_PRE)
expect(filtered.len()).to_equal(2)
```

</details>

#### excludes event types

1. var e1 = new diag event
2. var e2 = new diag event
   - Expected: filtered.len() equals `1`
   - Expected: filtered[0].event_type equals `EVENT_SESSION_START`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e1 = new_diag_event(EVENT_TOOL_PRE, "s1")
var e2 = new_diag_event(EVENT_SESSION_START, "s1")
val filtered = exclude_event_types([e1, e2], [EVENT_TOOL_PRE])
expect(filtered.len()).to_equal(1)
expect(filtered[0].event_type).to_equal(EVENT_SESSION_START)
```

</details>

#### merges two sorted timelines

1. var a1 = new diag event
2. var a2 = new diag event
3. var b1 = new diag event
   - Expected: merged.len() equals `3`
   - Expected: merged[0].timestamp equals `100`
   - Expected: merged[1].timestamp equals `200`
   - Expected: merged[2].timestamp equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a1 = new_diag_event("a", "s1")
a1.timestamp = 100
var a2 = new_diag_event("a", "s1")
a2.timestamp = 300
var b1 = new_diag_event("b", "s1")
b1.timestamp = 200
val merged = merge_timelines([a1, a2], [b1])
expect(merged.len()).to_equal(3)
expect(merged[0].timestamp).to_equal(100)
expect(merged[1].timestamp).to_equal(200)
expect(merged[2].timestamp).to_equal(300)
```

</details>

### formatters

#### formats tokens with K suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_tokens_k(500)).to_equal("500")
expect(format_tokens_k(1500)).to_equal("1.5K")
expect(format_tokens_k(10000)).to_equal("10.0K")
```

</details>

#### formats token usage as JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = TokenUsage(input_tokens: 100, output_tokens: 50, cache_read_input_tokens: 200, cache_creation_input_tokens: 30)
val json = format_token_usage_json(u)
expect(json).to_contain("\"input_tokens\":100")
expect(json).to_contain("\"output_tokens\":50")
expect(json).to_contain("\"total_input\":330")
```

</details>

#### formats event as JSON

1. var e = new diag event


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e = new_diag_event(EVENT_TOOL_PRE, "s123")
e.timestamp = 99999
val json = format_event_json(e)
expect(json).to_contain("\"event_type\":\"tool_pre\"")
expect(json).to_contain("\"session_id\":\"s123\"")
```

</details>

#### formats session as text

1. var session = new session diag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = new_session_diag("test-abc")
session.turn_count = 5
val text_out = format_session_text(session)
expect(text_out).to_contain("LLM Diagnostics")
expect(text_out).to_contain("test-abc")
```

</details>

### mcp_tracker

#### computes total calls across servers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = McpServerStats(server_name: "a", call_count: 5, total_request_bytes: 0, total_response_bytes: 0, total_latency_ms: 100, estimated_request_tokens: 10, estimated_response_tokens: 20, calls: [])
val s2 = McpServerStats(server_name: "b", call_count: 3, total_request_bytes: 0, total_response_bytes: 0, total_latency_ms: 50, estimated_request_tokens: 5, estimated_response_tokens: 10, calls: [])
expect(mcp_total_calls([s1, s2])).to_equal(8)
expect(mcp_total_estimated_tokens([s1, s2])).to_equal(45)
```

</details>

#### formats server summary line

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = McpServerStats(server_name: "simple-mcp", call_count: 10, total_request_bytes: 0, total_response_bytes: 0, total_latency_ms: 500, estimated_request_tokens: 100, estimated_response_tokens: 200, calls: [])
val line = mcp_server_summary_line(s)
expect(line).to_contain("simple-mcp")
expect(line).to_contain("10 calls")
expect(line).to_contain("50ms")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/llm_diagnostics/llm_diagnostics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM Diagnostics
- types
- token_estimator
- hook_handler
- cache_analyzer
- collector
- timeline
- formatters
- mcp_tracker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
