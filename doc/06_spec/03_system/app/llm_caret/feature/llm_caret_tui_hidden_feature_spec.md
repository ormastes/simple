# LLM Caret TUI and Hidden-Feature System Spec

> Exercises the production Caret TUI submission state transition without a live terminal or paid provider. The scenarios drive the input widget model through `run_chat_tui_submission`, dummy responder, transcript renderer, permission gate, retry policy, Claude REPL error route, and production hidden-command dispatch/admission. Provider, model, resume, and new-conversation commands must refresh visible state; a new conversation must receive a fresh session ID. The pure raw-key decoder and input-widget transition are covered; live PTY reads and terminal frame timing are not claimed by this component spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret TUI and Hidden-Feature System Spec

Exercises the production Caret TUI submission state transition without a live terminal or paid provider. The scenarios drive the input widget model through `run_chat_tui_submission`, dummy responder, transcript renderer, permission gate, retry policy, Claude REPL error route, and production hidden-command dispatch/admission. Provider, model, resume, and new-conversation commands must refresh visible state; a new conversation must receive a fresh session ID. The pure raw-key decoder and input-widget transition are covered; live PTY reads and terminal frame timing are not claimed by this component spec.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the production Caret TUI submission state transition without a live
terminal or paid provider. The scenarios drive the input widget model through
`run_chat_tui_submission`, dummy responder, transcript renderer, permission
gate, retry policy, Claude REPL error route, and production hidden-command
dispatch/admission. Provider, model, resume, and new-conversation commands must
refresh visible state; a new conversation must receive a fresh session ID. The
pure raw-key decoder and input-widget transition are covered; live PTY reads
and terminal frame timing are not claimed by this component spec.

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LLM-CARET-FULL-003
# @req REQ-LLM-CARET-FULL-006
```

</details>

#### should apply raw terminal navigation without leaking escape bytes

- should apply raw terminal navigation without leaking escape bytes
- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: decoder_state equals `0`
   - Expected: input.value equals `>abc!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply raw terminal navigation without leaking escape bytes")
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

#### should reduce raw editing paging and Enter to one prompt

- should reduce raw editing paging and Enter to one prompt
- Open the caret TUI
- Edit a Unicode prompt and request both paging directions
   - Expected: edited.action equals `RAW_LINE_CONTINUE`
   - Expected: older.action equals `RAW_LINE_PAGE_UP`
   - Expected: newer.action equals `RAW_LINE_PAGE_DOWN`
- Submit one prompt without raw-byte leakage
   - Expected: submitted.action equals `RAW_LINE_SUBMIT`
   - Expected: submitted.submitted equals `hi한`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reduce raw editing paging and Enter to one prompt")
step("Open the caret TUI")
var state = make_raw_line_state(
    make_chat_tui_with_status(
        "llm_caret - dummy",
        "provider=dummy model=dummy-hello session=raw-session"
    ).input
)

step("Edit a Unicode prompt and request both paging directions")
for b in [104, 105, 33, 127, 0xED, 0x95, 0x9C]:
    val edited = step_raw_line_byte(state, b)
    expect(edited.action).to_equal(RAW_LINE_CONTINUE)
    state = edited.state
val older = step_raw_line_byte(state, 16)
val newer = step_raw_line_byte(state, 14)
expect(older.action).to_equal(RAW_LINE_PAGE_UP)
expect(newer.action).to_equal(RAW_LINE_PAGE_DOWN)

step("Submit one prompt without raw-byte leakage")
val submitted = step_raw_line_byte(state, 13)
expect(submitted.action).to_equal(RAW_LINE_SUBMIT)
expect(submitted.submitted).to_equal("hi한")
expect(submitted.submitted.contains("[")).to_be(false)
```

</details>

#### should surface provider switching through the visible transcript

- should surface provider switching through the visible transcript
- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: switched.ui.title equals `llm_caret - openai_compat`
   - Expected: tui_transcript_line_text(0) equals `System: provider set to openai_compat`
   - Expected: resumed.conversation.len() equals `1`
   - Expected: tui_transcript_line_text(0) equals `You: restored`
   - Expected: started.conversation.len() equals `0`
   - Expected: started.session_id equals `new-session`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should surface provider switching through the visible transcript")
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

- should show permission-denied tool output without executing the command
- Open the caret TUI
- Send a prompt through the visible input
- Check transcript and status
   - Expected: PERSIST_COUNT equals `1`
   - Expected: PERSIST_SESSION equals `permission-session`
   - Expected: tui_transcript_len() equals `3`
   - Expected: tui_transcript_line_text(0) equals `You: run a command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should show permission-denied tool output without executing the command")
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

- should expose bounded retry decisions and the terminal error route
- Open the caret TUI
   - Expected: queryEventRoute("error", false, false) equals `show query error`
- Send a prompt through the visible input
- Check transcript and status
   - Expected: effective_delay_ms(1, policy, 75) equals `75`
   - Expected: effective_delay_ms(1, policy, 1000) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose bounded retry decisions and the terminal error route")
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

- should resolve the hidden debug command while excluding it from visible commands
- Enable the hidden-feature fixture
- Check the hidden-feature gate
   - Expected: check_hidden_feature_gate(case, lookup) equals `hidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should resolve the hidden debug command while excluding it from visible commands")
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
# Reproduce (2026-08-25): comparing against a different command name
# could never hold (`/debug-tool-call` vs `/not-registered`). A gated
# hidden name must render exactly like an unknown command of the SAME
# name (line ~482 below pins the alias form the same way).
val unknown = dispatch_slash(
    "not-registered", "", _hooks("hidden-session")
)
expect(rejected.message).to_equal(
    "Unknown command: /debug-tool-call (try /help)"
)
expect(rejected.message.replace("debug-tool-call", "not-registered")).to_equal(
    unknown.message
)
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

- should reject disabled commands even when hidden features are enabled
- Enable the hidden-feature fixture
- Check the hidden-feature gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject disabled commands even when hidden features are enabled")
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

#### should preserve TUI state and suppress model persistence for hidden aliases

- should preserve TUI state and suppress model persistence for hidden aliases
- Enable the hidden-feature fixture
   - Expected: rejected.conversation equals `seeded`
   - Expected: rejected.session_id equals `hidden-session`
   - Expected: rejected.ui.title equals `ui.title`
   - Expected: rejected.ui.status equals `ui.status`
   - Expected: rejected.ui.input.value equals ``
   - Expected: MODEL_COUNT equals `0`
   - Expected: PERSIST_COUNT equals `0`
- Dispatch the admitted hidden alias through TUI submission
   - Expected: admitted.conversation equals `seeded`
   - Expected: admitted.session_id equals `hidden-session`
   - Expected: admitted.ui.title equals `ui.title`
   - Expected: admitted.ui.status equals `ui.status`
   - Expected: MODEL_COUNT equals `0`
   - Expected: PERSIST_COUNT equals `0`
- Check disabled alias rejection and zero side effects
   - Expected: disabled.conversation equals `seeded`
   - Expected: disabled.session_id equals `hidden-session`
   - Expected: disabled.ui.title equals `ui.title`
   - Expected: disabled.ui.status equals `ui.status`
   - Expected: MODEL_COUNT equals `0`
   - Expected: PERSIST_COUNT equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve TUI state and suppress model persistence for hidden aliases")
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=hidden-session"
)
val seeded = [new_user_message("seed")]

step("Enable the hidden-feature fixture")
tui_transcript_reset()
MODEL_COUNT = 0
PERSIST_COUNT = 0
val rejected = run_chat_tui_submission(
    ui, seeded, "hidden-session", "/debug_tool_call",
    default_policy(WORKSPACE_ROOT), _tui_fixture_model,
    _hooks("hidden-session")
)
expect(rejected.submitted_to_model).to_be(false)
expect(rejected.conversation).to_equal(seeded)
expect(rejected.session_id).to_equal("hidden-session")
expect(rejected.ui.title).to_equal(ui.title)
expect(rejected.ui.status).to_equal(ui.status)
expect(rejected.ui.input.value).to_equal("")
expect(tui_transcript_line_text(0)).to_equal(
    "System: Unknown command: /debug_tool_call (try /help)"
)
expect(MODEL_COUNT).to_equal(0)
expect(PERSIST_COUNT).to_equal(0)

step("Dispatch the admitted hidden alias through TUI submission")
tui_transcript_reset()
val admitted = run_chat_tui_submission(
    ui, seeded, "hidden-session", "/debug_tool_call",
    default_policy(WORKSPACE_ROOT), _tui_fixture_model,
    _hooks_hidden("hidden-session")
)
expect(admitted.submitted_to_model).to_be(false)
expect(admitted.conversation).to_equal(seeded)
expect(admitted.session_id).to_equal("hidden-session")
expect(admitted.ui.title).to_equal(ui.title)
expect(admitted.ui.status).to_equal(ui.status)
expect(tui_transcript_line_text(0)).to_equal(
    "System: Usage: /debug-tool-call <tool_use_json>"
)
expect(MODEL_COUNT).to_equal(0)
expect(PERSIST_COUNT).to_equal(0)

step("Check disabled alias rejection and zero side effects")
tui_transcript_reset()
val disabled = run_chat_tui_submission(
    ui, seeded, "hidden-session", "/remote_setup",
    default_policy(WORKSPACE_ROOT), _tui_fixture_model,
    _hooks_hidden("hidden-session")
)
expect(disabled.submitted_to_model).to_be(false)
expect(disabled.conversation).to_equal(seeded)
expect(disabled.session_id).to_equal("hidden-session")
expect(disabled.ui.title).to_equal(ui.title)
expect(disabled.ui.status).to_equal(ui.status)
expect(tui_transcript_line_text(0)).to_equal(
    "System: Command disabled: /remote_setup"
)
expect(MODEL_COUNT).to_equal(0)
expect(PERSIST_COUNT).to_equal(0)
```

</details>

#### should keep SGTTI out of the normal Caret product and TUI entrypoints

- should keep SGTTI out of the normal Caret product and TUI entrypoints
- Enable the hidden-feature fixture
- Check the hidden-feature gate
   - Expected: _source_excludes_sgtti("src/app/llm_caret/main.spl") equals `excluded`
   - Expected: _source_excludes_sgtti("src/app/llm_caret/chat_tui.spl") equals `excluded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep SGTTI out of the normal Caret product and TUI entrypoints")
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
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_tui_hidden_feature.md`
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

- Canonical SPipe generation for source `3e788a528044f979906c560f19992f5a9096018b4c086cb57b88489bb2ff98d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e788a528044f979906c560f19992f5a9096018b4c086cb57b88489bb2ff98d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e788a528044f979906c560f19992f5a9096018b4c086cb57b88489bb2ff98d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **80/100**; blockers: **0**.

SSpec documentization score: 80/100
source: test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.md (current)
findings: 13 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:256:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should accept visible input and render provider transcript and status' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:256:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept visible input and render provider transcript and status' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:284:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply raw terminal navigation without leaking escape bytes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:284:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should apply raw terminal navigation without leaking escape bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:307:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reduce raw editing paging and Enter to one prompt' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:307:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reduce raw editing paging and Enter to one prompt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:334:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should surface provider switching through the visible transcript' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:334:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should surface provider switching through the visible transcript' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:382:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should show permission-denied tool output without executing the command' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl:413:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose bounded retry decisions and the terminal error route' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
