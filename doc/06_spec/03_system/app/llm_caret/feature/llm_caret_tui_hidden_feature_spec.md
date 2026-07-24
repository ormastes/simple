# LLM Caret TUI and Hidden-Feature System Spec

> Exercises the production Caret TUI submission transition without a live terminal or paid provider. The scenarios drive `run_chat_tui_submission`, ANSI navigation decoding, transcript rendering, permissions, persistence, retry decisions, and production hidden-command dispatch. Raw-terminal byte acquisition and frame timing remain a separate evidence boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret TUI and Hidden-Feature System Spec

Exercises the production Caret TUI submission transition without a live terminal or paid provider. The scenarios drive `run_chat_tui_submission`, ANSI navigation decoding, transcript rendering, permissions, persistence, retry decisions, and production hidden-command dispatch. Raw-terminal byte acquisition and frame timing remain a separate evidence boundary.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md |
| Plan | doc/03_plan/sys_test/llm_caret_tui_hidden_feature.md |
| Design | doc/05_design/llm_caret_claude_cli_full_parity.md |
| Research | doc/01_research/local/llm_caret_claude_cli_harden.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl` |
| Updated | 2026-07-24 |
| Generator | Manual synchronization; `simple spipe-docgen` rerun blocked |

## Overview

Exercises the production Caret TUI submission state transition without a live
terminal or paid provider. The scenarios drive `run_chat_tui_submission`,
ANSI navigation decoding, transcript rendering, permission handling,
persistence, retry decisions, and production hidden-command dispatch.
Provider, model, resume, and new-conversation
commands must refresh visible state; a new conversation must receive a fresh
session ID. The pure raw-key decoder and input-widget transition are covered;
live PTY reads and terminal frame timing remain outside this spec.

**Requirement IDs:** REQ-LLM-CARET-FULL-003, REQ-LLM-CARET-FULL-006
**Requirements:** doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md
**Plan:** doc/03_plan/sys_test/llm_caret_tui_hidden_feature.md
**Design:** doc/05_design/llm_caret_claude_cli_full_parity.md
**Research:** doc/01_research/local/llm_caret_claude_cli_harden.md
**TUI Captures:** build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature/caret_tui.txt

The SGTTI assertion is a source-boundary gate only. It proves the production
Caret entrypoint and TUI implementation do not import or construct the debug
surface; this spec does not claim a live PTY screenshot or terminal pixel proof.

## Syntax

The frozen `CaretTuiFeatureCase` and `CaretHiddenFeatureCase` fixtures keep the
visible-state and hidden-gate expectations explicit. Scenarios use only the
dummy provider and injected model responses; no paid API or user credential is
read.

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| Expected TUI Captures | 1 |
| Executed TUI Captures | 0 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `caret_tui.txt` | Expected TUI capture; not executed | `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature/caret_tui.txt` |

The executable runner is currently blocked, so the capture path above is an
expected artifact location, not passing runtime evidence. This manual was
synchronized from the executable source without running docgen.

## Scenarios

### REQ-LLM-CARET-FULL-003: LLM Caret TUI visible behavior

#### should accept visible input and render provider transcript and status

- Open the caret TUI
   - Expected: ui.input.value equals `case.prompt`
- Send a prompt through the visible input
   - Expected: tui_transcript_len() equals `2`
- Check transcript and status
   - Expected: check_tui_snapshot(snapshot, case) equals `matched`
   - Expected: dir_create_all(ARTIFACT_DIR) is true
   - Expected: file_write(TUI_CAPTURE_PATH, snapshot) is true
   - Expected: file_read(TUI_CAPTURE_PATH) equals `snapshot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val case = CaretTuiFeatureCase(
    prompt: "hello caret",
    provider: "dummy",
    model: "dummy-hello",
    session_id: "tui-session",
    expected_reply: "fixture-dummy-ok"
)

step("Open the caret TUI")
val ui = setup_tui_fixture(case)
expect(ui.input.value).to_equal(case.prompt)

step("Send a prompt through the visible input")
val snapshot = run_tui_action(case, ui)
expect(tui_transcript_len()).to_equal(2)

step("Check transcript and status")
expect(check_tui_snapshot(snapshot, case)).to_equal("matched")
expect(dir_create_all(ARTIFACT_DIR)).to_be(true)
expect(file_write(TUI_CAPTURE_PATH, snapshot)).to_be(true)
expect(file_read(TUI_CAPTURE_PATH)).to_equal(snapshot)
```

</details>

#### should apply raw terminal navigation without leaking escape bytes

- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: decoder_state equals `0`
   - Expected: input.value equals `>abc!`
   - Expected: input.value contains no `[` escape continuation


<details>
<summary>Executable SSpec</summary>

Complete executable scenario source.

```simple
step("Open the caret TUI")
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=key-session"
)
var input = input_insert_char(ui.input, "a")
input = input_insert_char(input, "c")
var decoder_state = 0

step("Send a prompt through the visible input")
for b in [27, 91, 68, 98, 27, 91, 72, 62, 27, 91, 70, 33]:
    val decoded = decode_raw_key_byte(decoder_state, b)
    decoder_state = decoded.state
    input = apply_raw_key_decode(input, decoded)

step("Check transcript and status")
expect(decoder_state).to_equal(0)
expect(input.value).to_equal(">abc!")
expect(input.value.contains("[")).to_be(false)
```

</details>

#### should surface provider switching through the visible transcript

- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: provider switch refreshes title/status without model submission
   - Expected: tui_transcript_line_text(0) equals `System: provider set to openai_compat`
   - Expected: resume restores session status, conversation, and transcript
   - Expected: new starts `new-session` with an empty conversation


<details>
<summary>Executable SSpec</summary>

Complete executable scenario source.

```simple
step("Open the caret TUI")
tui_transcript_reset()
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=tui-session"
)

step("Send a prompt through the visible input")
val switched = run_chat_tui_submission(
    ui, [], "tui-session", "/provider openai_compat",
    default_policy(WORKSPACE_ROOT), _tui_fixture_model,
    _hooks("tui-session")
)

step("Check transcript and status")
expect(switched.ui.status).to_contain("provider=openai_compat")
expect(switched.ui.title).to_equal("llm_caret - openai_compat")
expect(switched.running).to_be(true)
expect(switched.submitted_to_model).to_be(false)
expect(tui_transcript_line_text(0)).to_equal("System: provider set to openai_compat")

val resumed = run_chat_tui_submission(
    switched.ui, switched.conversation, switched.session_id,
    "/resume tui-session", default_policy(WORKSPACE_ROOT),
    _tui_fixture_model, _hooks_with_resume("seed-session")
)
expect(resumed.ui.status).to_contain("session=tui-session")
expect(resumed.conversation.len()).to_equal(1)
expect(tui_transcript_line_text(0)).to_equal("You: restored")
expect(tui_transcript_line_text(1)).to_equal(
    "System: resumed session tui-session"
)

val started = run_chat_tui_submission(
    resumed.ui, resumed.conversation, resumed.session_id, "/new",
    default_policy(WORKSPACE_ROOT), _tui_fixture_model,
    _hooks("tui-session")
)
expect(started.conversation.len()).to_equal(0)
expect(started.session_id).to_equal("new-session")
expect(started.ui.status).to_contain("session=new-session")
expect(tui_transcript_line_text(0)).to_equal(
    "System: started a new conversation"
)
```

</details>

#### should show permission-denied tool output without executing the command

- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: result.submitted_to_model is true
   - Expected: persistence runs once for `permission-session`
   - Expected: transcript contains user, denied tool, and assistant lines


<details>
<summary>Executable SSpec</summary>

Complete executable scenario source.

```simple
step("Open the caret TUI")
tui_transcript_reset()
PERSIST_COUNT = 0
val policy = default_policy(WORKSPACE_ROOT)
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=permission-session"
)

step("Send a prompt through the visible input")
val result = run_chat_tui_submission(
    ui, [], "permission-session", "run a command",
    policy, _permission_tool, _hooks("permission-session")
)

step("Check transcript and status")
expect(result.submitted_to_model).to_be(true)
expect(PERSIST_COUNT).to_equal(1)
expect(PERSIST_SESSION).to_equal("permission-session")
expect(result.conversation.len()).to_be_greater_than(2)
expect(tui_transcript_len()).to_equal(3)
expect(tui_transcript_line_text(0)).to_equal("You: run a command")
expect(tui_transcript_line_text(1)).to_contain("tool bash [error]")
expect(tui_transcript_line_text(1)).to_contain("permission")
expect(tui_transcript_line_text(2)).to_equal(
    "Assistant: permission handled"
)
```

</details>

#### should expose bounded retry decisions and the terminal error route

- Open the caret TUI
   - Expected: queryEventRoute("error", false, false) equals `show query error`
- Send a prompt through the visible input
   - Expected: should_retry(429, 1, policy) is true
   - Expected: should_retry(503, 3, policy) is true
   - Expected: should_retry(503, 4, policy) is false
   - Expected: should_retry(400, 1, policy) is false
- Check transcript and status
   - Expected: effective_delay_ms(1, policy, 75) equals `75`
   - Expected: effective_delay_ms(1, policy, 1000) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = RetryPolicy(
    max_attempts: 4,
    base_delay_ms: 10,
    max_delay_ms: 100,
    timeout_ms: 1000
)

step("Open the caret TUI")
expect(queryEventRoute("error", false, false)).to_equal("show query error")

step("Send a prompt through the visible input")
expect(should_retry(429, 1, policy)).to_be(true)
expect(should_retry(503, 3, policy)).to_be(true)
expect(should_retry(503, 4, policy)).to_be(false)
expect(should_retry(400, 1, policy)).to_be(false)

step("Check transcript and status")
expect(effective_delay_ms(1, policy, 75)).to_equal(75)
expect(effective_delay_ms(1, policy, 1000)).to_equal(100)
```

</details>

### REQ-LLM-CARET-FULL-006: LLM Caret hidden-feature gate

#### should resolve the hidden debug command while excluding it from visible commands

- Enable the hidden-feature fixture
- Check the hidden-feature gate
   - Expected: check_hidden_feature_gate(case, lookup) equals `hidden`
   - Expected: disabled hidden and unknown commands return the same message
   - Expected: admitted inspection reports ID/name without secret input


<details>
<summary>Executable SSpec</summary>

Complete executable scenario source.

```simple
val case = CaretHiddenFeatureCase(
    command: "/debug-tool-call",
    alias: "debug_tool_call",
    expected_enabled: true,
    expected_hidden: true
)

step("Enable the hidden-feature fixture")
val lookup = setup_hidden_feature_fixture(case)

step("Check the hidden-feature gate")
expect(check_hidden_feature_gate(case, lookup)).to_equal("hidden")
expect(admitRootCommand(case.command, false).found).to_be(false)
val rejected = dispatch_slash(
    "debug-tool-call", "call-1", _hooks("hidden-session")
)
val unknown = dispatch_slash(
    "not-registered", "", _hooks("hidden-session")
)
expect(rejected.message).to_equal(unknown.message)
val executed = dispatch_slash(
    "debug-tool-call",
    "{\"type\":\"tool_use\",\"id\":\"call-1\",\"name\":\"bash\",\"input\":{\"command\":\"echo sk-ant-fixture-secret\"}}",
    _hooks_hidden("hidden-session")
)
expect(executed.message).to_contain("id=call-1")
expect(executed.message).to_contain("name=bash")
expect(executed.message.contains("sk-ant-fixture-secret")).to_be(false)
```

</details>

#### should reject disabled commands even when hidden features are enabled

- Enable the hidden-feature fixture
- Check the hidden-feature gate
   - Expected: disabled command metadata is retained
   - Expected: disabled commands are never admitted
   - Expected: production dispatch reports the command disabled


<details>
<summary>Executable SSpec</summary>

Complete executable scenario source.

```simple
step("Enable the hidden-feature fixture")
val metadata = findRootCommand("/remote-setup")
val admitted = admitRootCommand("/remote-setup", true)

step("Check the hidden-feature gate")
expect(metadata.found).to_be(true)
expect(metadata.command.enabled).to_be(false)
expect(admitted.found).to_be(false)
val dispatched = dispatch_slash(
    "remote-setup", "", _hooks_hidden("hidden-session")
)
expect(dispatched.message).to_contain("Command disabled")
```

</details>

#### should keep SGTTI out of the normal Caret product and TUI entrypoints

- Enable the hidden-feature fixture
   - Expected: lookup.command.hidden is true
- Check the hidden-feature gate
   - Expected: _source_excludes_sgtti("src/app/llm_caret/main.spl") equals `excluded`
   - Expected: _source_excludes_sgtti("src/app/llm_caret/chat_tui.spl") equals `excluded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val case = CaretHiddenFeatureCase(
    command: "/debug-tool-call",
    alias: "debug_tool_call",
    expected_enabled: true,
    expected_hidden: true
)

step("Enable the hidden-feature fixture")
val lookup = setup_hidden_feature_fixture(case)
expect(lookup.command.hidden).to_be(true)

step("Check the hidden-feature gate")
expect(_source_excludes_sgtti("src/app/llm_caret/main.spl")).to_equal("excluded")
expect(_source_excludes_sgtti("src/app/llm_caret/chat_tui.spl")).to_equal("excluded")
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

Execution status: not run in this synchronization because the executable
runner is blocked. Active means the scenarios are enabled in source; it does
not claim a runtime PASS.


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_tui_hidden_feature.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_full_parity.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>
