# LLM Caret TUI and Hidden-Feature System Spec

> Exercises the production Caret TUI submission transition without a live terminal or paid provider. The scenarios drive `run_chat_tui_submission`, transcript rendering, permissions, retry decisions, and production hidden-command dispatch. Raw-terminal key reading and frame timing remain a separate evidence boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret TUI and Hidden-Feature System Spec

Exercises the production Caret TUI submission transition without a live terminal or paid provider. The scenarios drive `run_chat_tui_submission`, transcript rendering, permissions, retry decisions, and production hidden-command dispatch. Raw-terminal key reading and frame timing remain a separate evidence boundary.

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
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the production Caret TUI submission state transition without a live
terminal or paid provider. The scenarios drive `run_chat_tui_submission`,
transcript rendering, permission handling, retry decisions, and production
hidden-command dispatch. Provider, model, resume, and new-conversation
commands must refresh visible state; a new conversation must receive a fresh
session ID. Raw-terminal key reading and frame timing remain outside this spec.

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
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `caret_tui.txt` | TUI capture | `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature/caret_tui.txt` |

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
    expected_reply: "hello"
)

step("Open the caret TUI")
val ui = setup_tui_fixture(case)
expect(ui.input.value).to_equal(case.prompt)

step("Send a prompt through the visible input")
val snapshot = run_tui_action(case, ui)
expect(tui_transcript_len()).to_equal(2)

step("Check transcript and status")
expect(check_tui_snapshot(snapshot, case)).to_equal("matched")
expect(dir_create_all(ARTIFACT_DIR)).to_equal(true)
expect(file_write(TUI_CAPTURE_PATH, snapshot)).to_equal(true)
expect(file_read(TUI_CAPTURE_PATH)).to_equal(snapshot)
```

</details>

#### should surface provider switching through the visible transcript

- Open the caret TUI
- tui transcript reset
- Send a prompt through the visible input
- render turn
- Check transcript and status
   - Expected: refreshed.title equals `llm_caret - openai_compat`
   - Expected: switched.exit is false
   - Expected: tui_transcript_line_text(0) equals `System: provider set to openai_compat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open the caret TUI")
tui_transcript_reset()
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=tui-session"
)

step("Send a prompt through the visible input")
val switched = dispatch_slash("provider", "openai_compat", _hooks("tui-session"))
val refreshed = apply_slash_status(ui, switched)
render_turn("system", switched.message)

step("Check transcript and status")
expect(refreshed.status).to_contain("provider=openai_compat")
expect(refreshed.title).to_equal("llm_caret - openai_compat")
expect(switched.exit).to_equal(false)
expect(tui_transcript_line_text(0)).to_equal("System: provider set to openai_compat")
```

</details>

#### should show permission-denied tool output without executing the command

- Open the caret TUI
- tui transcript reset
- Send a prompt through the visible input
- [new user message
- Check transcript and status
   - Expected: result.tool_calls_made equals `1`
   - Expected: result.stopped_reason equals `end_turn`
   - Expected: tui_transcript_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open the caret TUI")
tui_transcript_reset()
val policy = default_policy(WORKSPACE_ROOT)

step("Send a prompt through the visible input")
val result = run_agent_loop_rendered(
    policy,
    [new_user_message("run a command")],
    _permission_tool,
    4,
    tui_tool_renderer
)

step("Check transcript and status")
expect(result.tool_calls_made).to_equal(1)
expect(result.stopped_reason).to_equal("end_turn")
expect(tui_transcript_len()).to_equal(1)
expect(tui_transcript_line_text(0)).to_contain("tool bash [error]")
expect(tui_transcript_line_text(0)).to_contain("permission")
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
expect(should_retry(429, 1, policy)).to_equal(true)
expect(should_retry(503, 3, policy)).to_equal(true)
expect(should_retry(503, 4, policy)).to_equal(false)
expect(should_retry(400, 1, policy)).to_equal(false)

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


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
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

step("Check the hidden-feature gate")
expect(check_hidden_feature_gate(case, lookup)).to_equal("hidden")
expect(admitRootCommand(case.command, false).found).to_be(false)
```

</details>

#### should reject disabled commands even when hidden features are enabled

- Enable the hidden-feature fixture
- Check the hidden-feature gate
   - Expected: disabled command metadata is retained
   - Expected: disabled commands are never admitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enable the hidden-feature fixture")
val metadata = findRootCommand("/remote-setup")
val admitted = admitRootCommand("/remote-setup", true)

step("Check the hidden-feature gate")
expect(metadata.found).to_be(true)
expect(metadata.command.enabled).to_be(false)
expect(admitted.found).to_be(false)
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
expect(lookup.command.hidden).to_equal(true)

step("Check the hidden-feature gate")
expect(_source_excludes_sgtti("src/app/llm_caret/main.spl")).to_equal("excluded")
expect(_source_excludes_sgtti("src/app/llm_caret/chat_tui.spl")).to_equal("excluded")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_tui_hidden_feature.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_full_parity.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>
