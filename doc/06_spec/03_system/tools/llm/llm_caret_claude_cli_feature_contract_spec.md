# LLM Caret Claude CLI Feature Contract

> This offline system specification exercises the accepted Claude CLI feature map without network access. The provider cases use the production argument builder, structured-response parser, and dispatch path with a local executable fixture. Hidden command checks use production fast-mode and remote-review command gates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Claude CLI Feature Contract

This offline system specification exercises the accepted Claude CLI feature map without network access. The provider cases use the production argument builder, structured-response parser, and dispatch path with a local executable fixture. Hidden command checks use production fast-mode and remote-review command gates.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md |
| Plan | doc/03_plan/sys_test/llm_caret_claude_cli_full_parity.md |
| Design | doc/05_design/llm_caret_claude_cli_full_parity.md |
| Research | doc/01_research/local/llm_caret_claude_cli_harden.md |
| Source | `test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This offline system specification exercises the accepted Claude CLI feature
map without network access. The provider cases use the production argument
builder, structured-response parser, and dispatch path with a local executable
fixture. Hidden command checks use production fast-mode and remote-review
command gates.

The fixture intentionally does not execute `claude`; paid live acceptance is a
separate opt-in lane.

## Scope

The specification covers:

- accepted feature-map presence;
- the CLI capsule row;
- fast-command mapping;
- review-command mapping;
- prompt argument construction;
- JSON output selection;
- model selection;
- system-prompt forwarding;
- session resume;
- maximum-turn forwarding;
- omission of Claude Code's removed maximum-token flag;
- structured-output schema forwarding;
- allowed-tool forwarding;
- extra-argument forwarding;
- verbose-output selection;
- mandatory verbose mode for stream-json;
- Claude Code system, assistant, and result stream envelopes;
- aggregation of multiple assistant text blocks;
- JSON-schema `structured_output` result envelopes;
- rejection of malformed or contract-free JSON responses;
- direct `claude_cli_send` response-field and failure-path behavior;
- offline production subprocess dispatch;
- offline NDJSON stream subprocess dispatch, empty/malformed output rejection,
  and terminal-event enforcement;
- subprocess-error secret redaction;
- protocol-level stream error/result secret redaction;
- public `llm_init_defaults`/`llm_init`/`llm_send`/`llm_chat` routing;
- public initialization isolation and failed-session rejection;
- successful structured responses;
- usage counters;
- structured provider errors;
- default stop reasons;
- fast-command disabled visibility;
- fast-command enabled visibility;
- disabled-gate side-effect prevention;
- permanently hidden remote review metadata.

The specification does not cover:

- live authentication;
- remote billing;
- Claude service availability;
- terminal rendering;
- full-screen TUI input;
- browser or Metal GUI rendering;
- network retry timing;
- provider rate limits.

## Syntax

```bash
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl --output doc/06_spec --no-index
```

## Accepted Feature Map

The accepted inventory is
`doc/03_plan/trace/llm_caret_claude_cli_full_parity_feature_matrix.tsv`.
The scenario requires rows for the top-level CLI capsule and the two hidden
feature witnesses used by this test. Missing rows fail before provider behavior
is accepted.

## Frozen Test Interface

`CaretCliFeatureCase` carries one deterministic provider request and response.
The helper vocabulary is frozen for parallel CLI and TUI work:

- `setup_cli_fixture`
- `run_cli_case`
- `check_cli_result`
- `setup_hidden_feature_fixture`
- `check_hidden_feature_gate`

Displayed manual flow uses these exact steps:

1. `Load the accepted Claude feature map`
2. `Invoke the caret CLI provider`
3. `Check the structured CLI response`
4. `Enable the hidden-feature fixture`
5. `Check the hidden-feature gate`

## Provider Cases

### Single Shot

The first case proves the required prompt, JSON output format, model, and
maximum-turn arguments. Its response proves content, model identity, session
identity, token usage, and a non-error status.

### Resume With Tools

The second case adds a system prompt, an existing session identifier, and two
allowed tools. The structured response uses the alternative token-usage field
names accepted by the production parser.

### Structured Error

The third case proves an `is_error` response becomes a structured error with
the `error` stop reason. It is an executable reject path, not a placeholder
pass.

## Hidden Feature Contract

The fast command is hidden and disabled when its feature gate is false. Enabling
the fixture exposes the command and preserves its immediate-command metadata.
Calling the disabled command must not prefetch, switch models, or enable fast
mode.

Remote review is a distinct permanently hidden command. Its hidden status is
checked separately so an enabled fast fixture cannot accidentally make every
hidden command visible.

## Failure Handling

The test fails when:

- the accepted map is absent;
- a required feature row is absent;
- argument construction drops a configured field;
- the production provider bypasses the tested wrapper;
- the public convenience API bypasses the tested wrapper;
- a removed Claude flag reaches the subprocess;
- structured response parsing loses content or usage;
- an error response is accepted as success;
- disabled fast mode becomes visible;
- a disabled command performs prefetch work;
- the remote review command becomes visible.

## Safety

All provider responses come from local immutable fixtures. The executable
fixture rejects removed flags and never accesses the network. No Claude process
is started, no API key is read, and no paid API call can occur from this file.

## Evidence

A passing run proves the production CLI builder/parser and hidden-command gate
functions satisfy this bounded contract. It complements, but does not replace,
the traceability, full-parity inventory, implementation, and opt-in live gates.

## Scenarios

### LLM caret Claude CLI feature contract

### REQ-LLM-CARET-FULL-003: accepted CLI provider features

#### should map production CLI argument and response behavior
#### should reject malformed and contract-free response envelopes

- should reject malformed and contract-free response envelopes
- Parse invalid single-shot response envelopes
- Check typed response validation
- Parse invalid stream envelopes
- Check typed stream validation
   - Expected: forged.stop_reason equals `invalid`
   - Expected: empty_result.stop_reason equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject malformed and contract-free response envelopes")
step("Parse invalid single-shot response envelopes")
val malformed = parse_claude_json_response("not-json")
val missing = parse_claude_json_response("{}")
val wrong_type = parse_claude_json_response(
    "{\"result\":{},\"is_error\":false}"
)

step("Check typed response validation")
expect(malformed.is_error).to_be(true)
expect(missing.error).to_contain("missing result")
expect(wrong_type.error).to_contain("must be a string")

step("Parse invalid stream envelopes")
val forged = parse_claude_stream_line(
    "{\"type\":\"forged_terminal\",\"result\":\"done\"}"
)
val empty_result = parse_claude_stream_line(
    "{\"type\":\"result\"}"
)

step("Check typed stream validation")
expect(forged.stop_reason).to_equal("invalid")
expect(forged.content).to_contain("unsupported")
expect(empty_result.stop_reason).to_equal("invalid")
expect(empty_result.content).to_contain("missing result")
```

</details>

#### should forward schema tools and extras through production dispatch

- should forward schema tools and extras through production dispatch
- Invoke baseline Claude CLI provider dispatch
- Check baseline dispatch and redaction
   - Expected: baseline.content equals `fixture-ok`
   - Expected: baseline.session_id equals `resume-1`
   - Expected: baseline.input_tokens equals `11`
   - Expected: baseline.output_tokens equals `3`
   - Expected: baseline_error.stop_reason equals `error`
- Invoke advanced Claude CLI provider dispatch
- Check advanced argument forwarding
   - Expected: response.content equals `advanced-ok`
- Reject advanced CLI arguments for another provider


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should forward schema tools and extras through production dispatch")
step("Invoke baseline Claude CLI provider dispatch")
val baseline = dispatch_send(
    "claude_cli", "fixture-success", "sonnet", "", "", MOCK_CLAUDE,
    "Be concise", "resume-1", 2, 4096, "[]"
)
val baseline_error = dispatch_send(
    "claude_cli", "fixture-error", "sonnet", "", "", MOCK_CLAUDE,
    "", "", 0, 4096, "[]"
)

step("Check baseline dispatch and redaction")
expect(baseline.is_error).to_be(false)
expect(baseline.content).to_equal("fixture-ok")
expect(baseline.session_id).to_equal("resume-1")
expect(baseline.input_tokens).to_equal(11)
expect(baseline.output_tokens).to_equal(3)
expect(baseline_error.is_error).to_be(true)
expect(baseline_error.stop_reason).to_equal("error")
expect(baseline_error.error).to_contain("[REDACTED:")
expect(baseline_error.error.contains("sk-ant-fixture-secret")).to_be(false)

step("Invoke advanced Claude CLI provider dispatch")
val response = dispatch_send_advanced(
    "claude_cli", "fixture-advanced", "sonnet", "", "",
    MOCK_CLAUDE, "", "", 0, 0, "[]",
    "{\"type\":\"object\"}", ["Read"], ["--fixture-extra"]
)

step("Check advanced argument forwarding")
expect(response.is_error).to_be(false)
expect(response.content).to_equal("advanced-ok")

step("Reject advanced CLI arguments for another provider")
val rejected = dispatch_send_advanced(
    "dummy", "ignored", "", "", "", "", "", "", 0, 0, "[]",
    "{\"type\":\"object\"}", [], []
)
expect(rejected.is_error).to_be(true)
expect(rejected.error).to_contain("require claude_cli")
```

</details>

#### should preserve and redact a provider stream error

- should preserve and redact a provider stream error
- Build and parse valid stream envelopes
- Check valid stream envelopes
   - Expected: init_event.event_type equals `system`
   - Expected: init_event.session_id equals `stream-session`
   - Expected: assistant_event.event_type equals `assistant`
   - Expected: assistant_event.content equals `streamed`
   - Expected: result_event.event_type equals `result`
   - Expected: result_event.content equals `complete`
   - Expected: result_event.output_tokens equals `2`
   - Expected: structured_event.event_type equals `result`
   - Expected: structured_event.content equals `{"answer":42}`
- Invoke complete and fail-closed stream fixtures
- Check stream completion and fail-closed errors
   - Expected: stream_events.len() equals `3`
   - Expected: stream_events[0].event_type equals `system`
   - Expected: stream_events[0].session_id equals `stream-session`
   - Expected: stream_events[1].event_type equals `assistant`
   - Expected: stream_events[1].content equals `streamed fixture`
   - Expected: stream_events[2].event_type equals `result`
   - Expected: stream_events[2].content equals `stream complete`
   - Expected: stream_events[2].output_tokens equals `3`
   - Expected: stream_errors.len() equals `1`
   - Expected: stream_errors[0].event_type equals `error`
   - Expected: empty_stream.len() equals `1`
   - Expected: empty_stream[0].event_type equals `error`
   - Expected: malformed_stream.len() equals `1`
   - Expected: malformed_stream[0].event_type equals `error`
   - Expected: malformed_stream[0].stop_reason equals `invalid`
   - Expected: mixed_stream.len() equals `1`
   - Expected: mixed_stream[0].stop_reason equals `invalid`
   - Expected: duplicate_terminal.len() equals `1`
   - Expected: duplicate_terminal[0].stop_reason equals `invalid`
   - Expected: stop_then_result.len() equals `2`
   - Expected: stop_then_result[0].event_type equals `message_stop`
   - Expected: stop_then_result[1].event_type equals `result`
   - Expected: stop_then_result[1].content equals `complete`
   - Expected: incomplete_stream.len() equals `2`
   - Expected: incomplete_stream[1].event_type equals `error`
   - Expected: protocol_error.len() equals `1`
   - Expected: protocol_error[0].stop_reason equals `error`
- Invoke the provider-error NDJSON fixture
- Check the structured stream error
   - Expected: events.len() equals `1`
   - Expected: events[0].event_type equals `error`
   - Expected: events[0].stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 114 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve and redact a provider stream error")
step("Build and parse valid stream envelopes")
val stream_args = build_claude_stream_args(
    "stream prompt", "sonnet", "Be concise", "", 1
)
val init_event = parse_claude_stream_line(
    "{\"type\":\"system\",\"subtype\":\"init\",\"session_id\":\"stream-session\",\"model\":\"claude-sonnet-4-6\"}"
)
val assistant_event = parse_claude_stream_line(
    "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"text\",\"text\":\"streamed\"}],\"usage\":{\"input_tokens\":3,\"output_tokens\":1}},\"session_id\":\"stream-session\"}"
)
val result_event = parse_claude_stream_line(
    "{\"type\":\"result\",\"subtype\":\"success\",\"is_error\":false,\"result\":\"complete\",\"session_id\":\"stream-session\",\"usage\":{\"input_tokens\":3,\"output_tokens\":2}}"
)
val structured_event = parse_claude_stream_line(
    "{\"type\":\"result\",\"subtype\":\"success\",\"is_error\":false,\"structured_output\":{\"answer\":42},\"session_id\":\"stream-session\"}"
)

step("Check valid stream envelopes")
expect(stream_args).to_contain("stream-json")
expect(stream_args).to_contain("--verbose")
expect(init_event.event_type).to_equal("system")
expect(init_event.session_id).to_equal("stream-session")
expect(assistant_event.event_type).to_equal("assistant")
expect(assistant_event.content).to_equal("streamed")
expect(result_event.event_type).to_equal("result")
expect(result_event.content).to_equal("complete")
expect(result_event.output_tokens).to_equal(2)
expect(structured_event.event_type).to_equal("result")
expect(structured_event.content).to_equal("{\"answer\":42}")

step("Invoke complete and fail-closed stream fixtures")
val stream_events = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream", "sonnet", "Be concise", "", 1
)
val stream_errors = claude_cli_stream(
    MOCK_CLAUDE, "fixture-error", "sonnet", "", "", 1
)
val empty_stream = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-empty", "sonnet", "", "", 1
)
val malformed_stream = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-malformed", "sonnet", "", "", 1
)
val mixed_stream = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-malformed-then-result",
    "sonnet", "", "", 1
)
val duplicate_terminal = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-duplicate-terminal",
    "sonnet", "", "", 1
)
val stop_then_result = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-stop-then-result",
    "sonnet", "", "", 1
)
val incomplete_stream = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-incomplete", "sonnet", "", "", 1
)
val protocol_error = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-secret-error", "sonnet", "", "", 1
)

step("Check stream completion and fail-closed errors")
expect(stream_events.len()).to_equal(3)
expect(stream_events[0].event_type).to_equal("system")
expect(stream_events[0].session_id).to_equal("stream-session")
expect(stream_events[1].event_type).to_equal("assistant")
expect(stream_events[1].content).to_equal("streamed fixture")
expect(stream_events[2].event_type).to_equal("result")
expect(stream_events[2].content).to_equal("stream complete")
expect(stream_events[2].output_tokens).to_equal(3)
expect(stream_errors.len()).to_equal(1)
expect(stream_errors[0].event_type).to_equal("error")
expect(stream_errors[0].content).to_contain("[REDACTED:")
expect(stream_errors[0].content.contains("sk-ant-fixture-secret")).to_be(false)
expect(empty_stream.len()).to_equal(1)
expect(empty_stream[0].event_type).to_equal("error")
expect(empty_stream[0].content).to_contain("no valid stream events")
expect(malformed_stream.len()).to_equal(1)
expect(malformed_stream[0].event_type).to_equal("error")
expect(malformed_stream[0].stop_reason).to_equal("invalid")
expect(malformed_stream[0].content).to_contain("invalid JSON")
expect(mixed_stream.len()).to_equal(1)
expect(mixed_stream[0].stop_reason).to_equal("invalid")
expect(mixed_stream[0].content).to_contain("invalid JSON")
expect(duplicate_terminal.len()).to_equal(1)
expect(duplicate_terminal[0].stop_reason).to_equal("invalid")
expect(duplicate_terminal[0].content).to_contain("after a terminal")
expect(stop_then_result.len()).to_equal(2)
expect(stop_then_result[0].event_type).to_equal("message_stop")
expect(stop_then_result[1].event_type).to_equal("result")
expect(stop_then_result[1].content).to_equal("complete")
expect(incomplete_stream.len()).to_equal(2)
expect(incomplete_stream[1].event_type).to_equal("error")
expect(incomplete_stream[1].content).to_contain("before a terminal event")
expect(protocol_error.len()).to_equal(1)
expect(protocol_error[0].stop_reason).to_equal("error")
expect(protocol_error[0].content.contains("sk-ant-fixture-secret")).to_be(false)

step("Invoke the provider-error NDJSON fixture")
val events = claude_cli_stream(
    MOCK_CLAUDE, "fixture-stream-provider-error",
    "sonnet", "", "", 1
)

step("Check the structured stream error")
expect(events.len()).to_equal(1)
expect(events[0].event_type).to_equal("error")
expect(events[0].stop_reason).to_equal("error")
expect(events[0].content).to_contain("provider overloaded")
expect(events[0].content).to_contain("[REDACTED:")
expect(events[0].content.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

#### should execute the direct Claude sender and fail closed

- should execute the direct Claude sender and fail closed
- Invoke the direct Claude CLI sender
- Check every direct response field
   - Expected: response.content equals `fixture-ok`
   - Expected: response.model equals `sonnet`
   - Expected: response.session_id equals `resume-1`
   - Expected: response.stop_reason equals `end_turn`
   - Expected: response.input_tokens equals `11`
   - Expected: response.output_tokens equals `3`
- Reject malformed output and a missing executable
   - Expected: missing.content equals ``
   - Expected: missing.stop_reason equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute the direct Claude sender and fail closed")
step("Invoke the direct Claude CLI sender")
val response = claude_cli_send(
    MOCK_CLAUDE, "fixture-success", "sonnet",
    "Be concise", "", 0, 0, "", [], []
)

step("Check every direct response field")
expect(response.is_error).to_be(false)
expect(response.content).to_equal("fixture-ok")
expect(response.model).to_equal("sonnet")
expect(response.session_id).to_equal("resume-1")
expect(response.stop_reason).to_equal("end_turn")
expect(response.input_tokens).to_equal(11)
expect(response.output_tokens).to_equal(3)
expect(response.raw).to_contain("fixture-ok")

step("Reject malformed output and a missing executable")
val malformed = claude_cli_send(
    MOCK_CLAUDE, "fixture-json-malformed", "sonnet",
    "", "", 0, 0, "", [], []
)
expect(malformed.is_error).to_be(true)
expect(malformed.error).to_contain("invalid JSON")
val stderr_error = claude_cli_send(
    MOCK_CLAUDE, "fixture-error", "sonnet",
    "", "", 0, 0, "", [], []
)
expect(stderr_error.is_error).to_be(true)
expect(stderr_error.error).to_contain("[REDACTED:")
expect(stderr_error.error.contains("sk-ant-fixture-secret")).to_be(false)
val missing = claude_cli_send(
    "/definitely/missing/llm-caret-claude", "ignored", "",
    "", "", 0, 0, "", [], []
)
expect(missing.is_error).to_be(true)
expect(missing.content).to_equal("")
expect(missing.stop_reason).to_equal("error")
```

</details>

#### should route the public API history and redact provider failures

- should route the public API history and redact provider failures
- Invoke successful public Claude CLI chat
- Check successful public history
   - Expected: response equals `fixture-ok`
   - Expected: llm_history_len() equals `2`
   - Expected: llm_history_role(0) equals `user`
   - Expected: llm_history_content(0) equals `fixture-success`
   - Expected: llm_history_role(1) equals `assistant`
   - Expected: llm_history_content(1) equals `fixture-ok`
- Invoke failing public Claude CLI chat
- Check redacted public failure history
   - Expected: llm_history_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should route the public API history and redact provider failures")
step("Invoke successful public Claude CLI chat")
llm_clear()
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("Be concise")
val response = llm_chat("fixture-success")

step("Check successful public history")
expect(response).to_equal("fixture-ok")
expect(llm_history_len()).to_equal(2)
expect(llm_history_role(0)).to_equal("user")
expect(llm_history_content(0)).to_equal("fixture-success")
expect(llm_history_role(1)).to_equal("assistant")
expect(llm_history_content(1)).to_equal("fixture-ok")
llm_clear()

step("Invoke failing public Claude CLI chat")
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
val failure = llm_chat("fixture-error")

step("Check redacted public failure history")
expect(failure).to_start_with("ERROR: ")
expect(failure).to_contain("[REDACTED:")
expect(failure.contains("sk-ant-fixture-secret")).to_be(false)
expect(llm_history_len()).to_equal(1)
llm_clear()
```

</details>

#### should isolate public initialization and failed provider sessions

- should isolate public initialization and failed provider sessions
- Reset public system prompt state on initialization
   - Expected: llm_send("fixture-no-system") equals `no-system-ok`
   - Expected: llm_provider() equals `claude_cli`
   - Expected: llm_model() equals `sonnet`
- Keep an error response from poisoning the provider session
   - Expected: llm_send("fixture-success") equals `fixture-ok`
- Restore public defaults
   - Expected: llm_provider() equals `claude_cli`
   - Expected: llm_model() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should isolate public initialization and failed provider sessions")
step("Reset public system prompt state on initialization")
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
llm_system("stale system prompt")
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
expect(llm_send("fixture-no-system")).to_equal("no-system-ok")
expect(llm_provider()).to_equal("claude_cli")
expect(llm_model()).to_equal("sonnet")

step("Keep an error response from poisoning the provider session")
llm_clear()
llm_init("claude_cli", "sonnet")
llm_set_cli_path(MOCK_CLAUDE)
val failure = llm_send("fixture-error-session")
expect(failure).to_start_with("ERROR: ")
expect(failure).to_contain("[REDACTED:")
llm_system("Be concise")
expect(llm_send("fixture-success")).to_equal("fixture-ok")

step("Restore public defaults")
llm_init_defaults()
expect(llm_provider()).to_equal("claude_cli")
expect(llm_model()).to_equal("")
llm_clear()
```

</details>

### REQ-LLM-CARET-FULL-006: hidden feature gates

#### should keep gated and permanently hidden commands unavailable

- should keep gated and permanently hidden commands unavailable
- Enable the hidden-feature fixture
   - Expected: fixtures.len() equals `2`
- Check the hidden-feature gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep gated and permanently hidden commands unavailable")
step("Enable the hidden-feature fixture")
val fixtures = setup_hidden_feature_fixture()
expect(fixtures.len()).to_equal(2)
step("Check the hidden-feature gate")
check_hidden_feature_gate(fixtures)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_claude_cli_full_parity.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_full_parity.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-FULL-003`
- `REQ-LLM-CARET-FULL-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `932941da98f8091125c13d6b17799ab4ecd835d659c0bf6e7cc1d89811e90ac5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `932941da98f8091125c13d6b17799ab4ecd835d659c0bf6e7cc1d89811e90ac5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `932941da98f8091125c13d6b17799ab4ecd835d659c0bf6e7cc1d89811e90ac5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl
mirror: doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.md (current)
findings: 14 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:313:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should map production CLI argument and response behavior' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:313:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should map production CLI argument and response behavior' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:382:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed and contract-free response envelopes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:382:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject malformed and contract-free response envelopes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:411:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should forward schema tools and extras through production dispatch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:411:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should forward schema tools and extras through production dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:454:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve and redact a provider stream error' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:454:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve and redact a provider stream error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:570:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the direct Claude sender and fail closed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl:611:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route the public API history and redact provider failures' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
