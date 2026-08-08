# LLM Caret Claude CLI Feature Contract

> This offline system specification exercises the accepted Claude CLI feature map without network access. The provider cases use the production argument builder, structured-response parser, and dispatch path with a local executable fixture. Hidden command checks use production fast-mode and remote-review command gates.

| Tests | Active | Skipped | Pending | Executed |
|-------|--------|---------|---------|---------:|
| 8 | 8 | 0 | 0 | 0 |

> Execution status: designed and manually synchronized. The current
> self-hosted runner cannot resolve its process-spawn boundary, so this manual
> does not claim an executable PASS.

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Claude CLI Feature Contract

This offline system specification exercises the accepted Claude CLI feature map without network access. The provider cases use the production argument builder and structured-response parser. Hidden command checks use production fast-mode and remote-review command gates.

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
| Updated | 2026-07-24 |
| Generator | Manual synchronization; executable docgen is runtime-blocked |

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

- Load the accepted Claude feature map
   - Expected: cases.len() equals `3`
- Invoke the caret CLI provider
- Check the structured CLI response
- check cli result


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the accepted Claude feature map")
expect(file_exists(FEATURE_MAP)).to_be(true)
val feature_map = file_read(FEATURE_MAP)
expect(feature_map).to_contain("\tcli\t")
expect(feature_map).to_contain("commands/fast")
expect(feature_map).to_contain("commands/review")

val cases = setup_cli_fixture()
expect(cases.len()).to_equal(3)
for case in cases:
    step("Invoke the caret CLI provider")
    val args = build_claude_args(
        case.prompt,
        case.model,
        "json",
        case.system_prompt,
        case.session_id,
        case.max_turns,
        case.max_tokens,
        case.json_schema,
        case.tools,
        case.extra_args,
        case.verbose
    )
    val response = run_cli_case(case)
    step("Check the structured CLI response")
    expect(args).to_contain("-p")
    expect(args).to_contain(case.prompt)
    expect(args).to_contain("--output-format")
    expect(args).to_contain("json")
    expect(args).to_contain("--max-turns")
    expect(args).to_contain(case.max_turns.to_text())
    var unsupported_count = 0
    for arg in args:
        if arg == "--max-tokens":
            unsupported_count = unsupported_count + 1
    expect(unsupported_count).to_equal(0)
    if case.json_schema != "":
        expect(args).to_contain("--json-schema")
        expect(args).to_contain(case.json_schema)
    if case.model != "":
        expect(args).to_contain("--model")
        expect(args).to_contain(case.model)
    if case.system_prompt != "":
        expect(args).to_contain("--system-prompt")
        expect(args).to_contain(case.system_prompt)
    if case.session_id != "":
        expect(args).to_contain("--resume")
        expect(args).to_contain(case.session_id)
    for tool in case.tools:
        expect(args).to_contain(tool)
    if case.tools.len() > 0:
        var allowed_tools_flags = 0
        for arg in args:
            if arg == "--allowedTools":
                allowed_tools_flags = allowed_tools_flags + 1
        expect(allowed_tools_flags).to_equal(1)
    for arg in case.extra_args:
        expect(args).to_contain(arg)
    if case.verbose:
        expect(args).to_contain("--verbose")
    check_cli_result(case, response)
```

</details>

#### should reject malformed and contract-free response envelopes

- Parse invalid single-shot response envelopes
   - Expected: malformed JSON, a missing result, and a non-string result fail.
- Check typed response validation
- Parse invalid stream envelopes
   - Expected: an unsupported event and a result without content are invalid.
- Check typed stream validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Invoke baseline Claude CLI provider dispatch
   - Expected: success preserves content, session, and usage.
   - Expected: failure preserves an error while redacting its secret.
- Check baseline dispatch and redaction
- Invoke advanced Claude CLI provider dispatch
- Check advanced argument forwarding
   - Expected: schema, tool, and extra arguments produce `advanced-ok`.
- Reject advanced CLI arguments for another provider
   - Expected: non-Claude providers reject Claude-only arguments.

<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Build and parse valid stream envelopes
   - Expected: stream arguments force `stream-json` and verbose output.
   - Expected: system, assistant, result, and structured-result fields survive.
- Check valid stream envelopes
- Invoke complete and fail-closed stream fixtures
- Check stream completion and fail-closed errors
   - Expected: complete streams retain all three events.
   - Expected: malformed/mixed streams and duplicate terminals fail closed.
   - Expected: `message_stop` followed by the final result remains valid.
- Invoke the provider-error NDJSON fixture
- Check the structured stream error
   - Expected: one provider diagnostic is preserved while its secret is redacted.

<details>
<summary>Executable SSpec</summary>

Runnable source: 112 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Invoke the direct Claude CLI sender
- Check every direct response field
   - Expected: content, model, session, stop reason, usage, and raw response survive.
- Reject malformed output and a missing executable
   - Expected: malformed stdout and a missing executable return structured errors.
   - Expected: direct-sender stderr is redacted and never exposes the fixture secret.

<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Invoke successful public Claude CLI chat
- Check successful public history
   - Expected: the exact user prompt and assistant response remain in history.
- Invoke failing public Claude CLI chat
- Check redacted public failure history
   - Expected: a failed assistant turn is not added and its secret is redacted.

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Reset public system prompt state on initialization
   - Expected: the new client does not inherit a stale prompt.
- Keep an error response from poisoning the provider session
   - Expected: the failed session is not reused by the next success.
- Restore public defaults
   - Expected: provider and model return to their default identities.

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Enable the hidden-feature fixture
   - Expected: fixtures.len() equals `2`
- Check the hidden-feature gate
- check hidden feature gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Executed scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_claude_cli_full_parity.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_full_parity.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>
