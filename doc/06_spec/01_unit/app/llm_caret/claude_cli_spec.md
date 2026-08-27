# Claude Cli Specification

> Source-synchronized unit manual. The current self-hosted SSpec runner is
> blocked before trustworthy scenario execution, so this document records
> 84 active scenarios and 0 executed scenarios.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 84 | 84 | 0 | 0 | 0 |

claude_cli_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=claude_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Cli Specification

## Scenarios

### build_claude_args - minimal

#### includes prompt with -p flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hello", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "-p")).to_equal(true)
expect(args_get_flag_value(args, "-p")).to_equal("Hello")
```

</details>

#### defaults to json output format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--output-format")).to_equal("json")
```

</details>

#### has no model flag when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--model")).to_equal(false)
```

</details>

#### has no system-prompt flag when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--system-prompt")).to_equal(false)
```

</details>

#### has no resume flag when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--resume")).to_equal(false)
```

</details>

### build_claude_args - model

#### includes model flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "claude-opus-4-20250514", "", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--model")).to_equal("claude-opus-4-20250514")
```

</details>

#### supports sonnet model

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "claude-sonnet-4-20250514", "", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--model")).to_equal("claude-sonnet-4-20250514")
```

</details>

### build_claude_args - system prompt

#### includes system prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "You are a pirate", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--system-prompt")).to_equal("You are a pirate")
```

</details>

### build_claude_args - session

#### includes session resume

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "abc-123", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--resume")).to_equal("abc-123")
```

</details>

### build_claude_args - max turns

#### includes max turns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 5, 0, "", [], [], false)
expect(args_get_flag_value(args, "--max-turns")).to_equal("5")
```

</details>

#### omits max turns when zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--max-turns")).to_equal(false)
```

</details>

### build_claude_args - max tokens

#### includes max tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 4096, "", [], [], false)
expect(args_get_flag_value(args, "--max-tokens")).to_equal("4096")
```

</details>

#### omits max tokens when zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--max-tokens")).to_equal(false)
```

</details>

### build_claude_args - streaming

#### uses stream-json format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "stream-json", "", "", 0, 0, "", [], [], false)
expect(args_get_flag_value(args, "--output-format")).to_equal("stream-json")
```

</details>

### build_claude_args - json schema

#### includes json schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = _LB() + _Q() + "type" + _Q() + ":" + _Q() + "object" + _Q() + _RB()
val args = build_claude_args("Hi", "", "", "", "", 0, 0, schema, [], [], false)
expect(args_get_flag_value(args, "--json-schema")).to_equal(schema)
```

</details>

#### omits json schema when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--json-schema")).to_equal(false)
```

</details>

### build_claude_args - tools

#### includes single tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", ["Read"], [], false)
expect(args_contain(args, "--allowedTools")).to_equal(true)
expect(args_get_flag_value(args, "--allowedTools")).to_equal("Read")
```

</details>

#### includes multiple tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", ["Read", "Write", "Bash"], [], false)
# Count --allowedTools occurrences
var count = 0
for arg in args:
    if arg == "--allowedTools":
        count = count + 1
expect(count).to_equal(3)
```

</details>

#### has no tools when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should have no tools when empty")
step("Verify: should have no tools when empty")
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--allowedTools")).to_equal(false)
```

</details>

### build_claude_args - verbose

#### includes verbose flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], true)
expect(args_contain(args, "--verbose")).to_equal(true)
```

</details>

#### omits verbose when false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], [], false)
expect(args_contain(args, "--verbose")).to_equal(false)
```

</details>

### build_claude_args - extra args

#### appends extra args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], ["--no-cache"], false)
expect(args_contain(args, "--no-cache")).to_equal(true)
```

</details>

#### skips empty extra args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("Hi", "", "", "", "", 0, 0, "", [], ["", "--flag", ""], false)
expect(args_contain(args, "--flag")).to_equal(true)
expect(args_contain(args, "")).to_equal(false)
```

</details>

### build_claude_args - combined

#### builds complete args

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = build_claude_args("prompt", "claude-opus-4-20250514", "json", "be helpful", "sess-1", 3, 2048, "", ["Read"], ["--no-cache"], true)
expect(args_get_flag_value(args, "-p")).to_equal("prompt")
expect(args_get_flag_value(args, "--model")).to_equal("claude-opus-4-20250514")
expect(args_get_flag_value(args, "--output-format")).to_equal("json")
expect(args_get_flag_value(args, "--system-prompt")).to_equal("be helpful")
expect(args_get_flag_value(args, "--resume")).to_equal("sess-1")
expect(args_get_flag_value(args, "--max-turns")).to_equal("3")
expect(args_get_flag_value(args, "--max-tokens")).to_equal("2048")
expect(args_contain(args, "--verbose")).to_equal(true)
expect(args_contain(args, "--no-cache")).to_equal(true)
```

</details>

### parse_claude_json_response - success

#### parses successful response

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hello world!", "claude-sonnet-4-20250514", "sess-abc")
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal("Hello world!")
expect(resp.model).to_equal("claude-sonnet-4-20250514")
expect(resp.session_id).to_equal("sess-abc")
expect(resp.is_error).to_equal(false)
```

</details>

#### parses token counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hi", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.input_tokens).to_equal(150)
expect(resp.output_tokens).to_equal(42)
```

</details>

#### parses stop reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hello world!", "claude-sonnet-4-20250514", "sess-abc")
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal("Hello world!")
expect(resp.model).to_equal("claude-sonnet-4-20250514")
expect(resp.session_id).to_equal("sess-abc")
expect(resp.is_error).to_equal(false)
```

</details>

#### parses token counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hi", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.input_tokens).to_equal(150)
expect(resp.output_tokens).to_equal(42)
```

</details>

#### parses stop reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hi", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

#### preserves raw json

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Hi", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.raw).to_equal(json)
```

</details>

### parse_claude_json_response - error

#### parses error response

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_error_json("Rate limited")
val resp = parse_claude_json_response(json)
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("Rate limited")
expect(resp.stop_reason).to_equal("error")
```

</details>

#### handles empty response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should handle empty response")
step("Verify: should handle empty response")
val resp = parse_claude_json_response("")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("empty response")
```

</details>

#### handles whitespace-only response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = parse_claude_json_response("   ")
expect(resp.is_error).to_equal(true)
expect(resp.error).to_equal("empty response")
```

</details>

### parse_claude_json_response - edge cases

#### handles missing model field

1. var json =  LB
2. json = json +  Q
3. json = json +  Q
4. json = json +  RB
   - Expected: resp.content equals `Hello`
   - Expected: resp.model equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var json = _LB()
json = json + _Q() + "result" + _Q() + ":" + _Q() + "Hello" + _Q() + ","
json = json + _Q() + "is_error" + _Q() + ":false"
json = json + _RB()
val resp = parse_claude_json_response(json)
expect(resp.content).to_equal("Hello")
expect(resp.model).to_equal("")
```

</details>

#### defaults stop reason to end_turn

1. var json =  LB
2. json = json +  Q
3. json = json +  Q
4. json = json +  RB
   - Expected: resp.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var json = _LB()
json = json + _Q() + "result" + _Q() + ":" + _Q() + "Done" + _Q() + ","
json = json + _Q() + "is_error" + _Q() + ":false"
json = json + _RB()
val resp = parse_claude_json_response(json)
expect(resp.stop_reason).to_equal("end_turn")
```

</details>

#### handles multiline result content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = mock_json("Line 1\\nLine 2", "model", "sess")
val resp = parse_claude_json_response(json)
expect(resp.content).to_contain("Line 1")
```

</details>

### parse_claude_stream_line

#### parses content_block_delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = mock_stream_line("content_block_delta", "Hello ")
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("content_block_delta")
expect(evt.content).to_equal("Hello ")
```

</details>

#### parses message_stop

1. var line =  LB
2. line = line +  Q
3. line = line +  Q
4. line = line +  RB
   - Expected: evt.event_type equals `message_stop`
   - Expected: evt.stop_reason equals `end_turn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = _LB()
line = line + _Q() + "type" + _Q() + ":" + _Q() + "message_stop" + _Q() + ","
line = line + _Q() + "stop_reason" + _Q() + ":" + _Q() + "end_turn" + _Q()
line = line + _RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("message_stop")
expect(evt.stop_reason).to_equal("end_turn")
```

</details>

#### parses message_start with model

1. var line =  LB
2. line = line +  Q
3. line = line +  Q
4. line = line +  RB
   - Expected: evt.event_type equals `message_start`
   - Expected: evt.model equals `claude-sonnet-4-20250514`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = _LB()
line = line + _Q() + "type" + _Q() + ":" + _Q() + "message_start" + _Q() + ","
line = line + _Q() + "model" + _Q() + ":" + _Q() + "claude-sonnet-4-20250514" + _Q()
line = line + _RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("message_start")
expect(evt.model).to_equal("claude-sonnet-4-20250514")
```

</details>

#### handles empty line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should handle empty line")
step("Verify: should handle empty line")
val evt = parse_claude_stream_line("")
expect(evt.event_type).to_equal("empty")
```

</details>

#### handles unknown type

1. var line =  LB
2. line = line +  Q
3. line = line +  RB
   - Expected: evt.event_type equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = _LB()
line = line + _Q() + "data" + _Q() + ":" + _Q() + "something" + _Q()
line = line + _RB()
val evt = parse_claude_stream_line(line)
expect(evt.event_type).to_equal("unknown")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

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

## should return one redacted terminal error for a failed subprocess

- should return one redacted terminal error for a failed subprocess
- Verify: should return one redacted terminal error for a failed subprocess
   - Expected: events.len() equals `1`
   - Expected: events[0].event_type equals `error`
   - Expected: events[0].stop_reason equals `error`

**Step:** Run the deterministic Claude fixture with `fixture-error`, which
exits nonzero and writes a secret-bearing diagnostic.

**Expected:** The stream wrapper returns exactly one `error` terminal event
with stop reason `error`, identifies exit code 7, redacts the diagnostic, and
never exposes the fixture secret.

## should return a redacted terminal error result from the stream fixture

**Group:** claude_cli_stream - local fixture

**Step:** Read the deterministic terminal `result` error envelope.

**Expected:** The wrapper returns exactly one `result` event with error stop
reason and redacted content, without exposing the fixture secret.

## should return a redacted terminal provider error from the stream fixture

**Group:** claude_cli_stream - local fixture

**Step:** Read the deterministic typed provider error envelope.

**Expected:** The wrapper returns exactly one `error` terminal event with error
stop reason and redacted content, without exposing the fixture secret.

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

## should reject an assistant event after message stop

- should reject an assistant event after message stop
- Verify: should reject an assistant event after message stop
   - Expected: events.len() equals `1`
   - Expected: events[0].event_type equals `error`
   - Expected: events[0].stop_reason equals `invalid`

**Step:** Receive a `message_stop` marker followed by an assistant envelope.

**Expected:** The stream wrapper rejects the out-of-order event as a single
invalid terminal error that identifies data after `message_stop`; the later
assistant content is not admitted.

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
| Total scenarios | 84 |
| Active scenarios | 84 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
