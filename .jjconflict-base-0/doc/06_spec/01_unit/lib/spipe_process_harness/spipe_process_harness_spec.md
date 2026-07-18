# Spipe Process Harness Specification

> <details>

<!-- sdn-diagram:id=spipe_process_harness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spipe_process_harness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spipe_process_harness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spipe_process_harness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spipe Process Harness Specification

## Scenarios

### SPipe process harness

### provider normalization

#### normalizes the three supported LLM providers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_provider("Claude Code")).to_equal("claude")
expect(normalize_provider("Codex GPT")).to_equal("codex")
expect(normalize_provider("Google Gemini")).to_equal("gemini")
```

</details>

#### keeps unknown provider names stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_provider("LocalAgent")).to_equal("localagent")
```

</details>

### state and event paths

#### uses the default feature when blank

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(state_path("")).to_equal(".spipe/spipe-process-harness/state.md")
expect(event_log_path("")).to_equal(".spipe/spipe-process-harness/events.jsonl")
```

</details>

#### uses feature-specific durable state

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(state_path("demo")).to_equal(".spipe/demo/state.md")
```

</details>

### hook metadata

#### lists Claude hook events

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = provider_hook_events("claude")
expect(events).to_contain("PreToolUse")
expect(events).to_contain("SessionStart")
```

</details>

#### lists Codex and Gemini lifecycle events

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_hook_events("codex")).to_contain("turn_finish")
expect(provider_hook_events("gemini")).to_contain("prompt_submit")
```

</details>

#### builds provider-specific hook command

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hook_command("gemini")).to_equal("bin/simple spipe-process-harness hook --provider gemini")
```

</details>

#### renders an append-only JSONL hook envelope

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = hook_jsonl("codex", "tool_start", "sid1", "gpt-5", "{\"x\":1}")
expect(line).to_contain("\"provider\":\"codex\"")
expect(line).to_contain("\"event\":\"tool_start\"")
expect(line).to_contain("\"session_id\":\"sid1\"")
expect(line).to_contain("\"model\":\"gpt-5\"")
expect(line).to_contain("\"raw\"")
```

</details>

### prevention gate

#### blocks missing state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = gate_from_state("", true)
expect(decision.allowed).to_equal(false)
expect(decision.exit_code).to_equal(2)
```

</details>

#### blocks when approval is required and absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = render_state("demo", "request", "goal", false)
val decision = gate_from_state(state, true)
expect(decision.allowed).to_equal(false)
expect(decision.reason).to_equal("user approval missing")
```

</details>

#### allows approved state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = render_state("demo", "request", "goal", true)
val decision = gate_from_state(state, true)
expect(decision.allowed).to_equal(true)
expect(decision.exit_code).to_equal(0)
```

</details>

#### blocks explicit prevention marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = gate_from_state("User Approved: true\nPrevent: block\n", true)
expect(decision.allowed).to_equal(false)
expect(decision.reason).to_equal("SPipe prevention gate is blocking")
```

</details>

#### blocks failed status marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = gate_from_state("User Approved: true\nSTATUS: FAIL\n", true)
expect(decision.allowed).to_equal(false)
expect(decision.reason).to_equal("SPipe prevention gate is blocking")
```

</details>

### HUD and deploy

#### renders compact CLI HUD

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = HudSnapshot(
    model: "gpt-5",
    jj_worktree: "abc",
    commit_id: "def feat",
    hours_remaining: "3",
    week_remaining: "12",
    goal: "ship"
)
val hud = render_hud(snapshot)
expect(hud).to_contain("model=gpt-5")
expect(hud).to_contain("jj=abc")
expect(hud).to_contain("goal=ship")
```

</details>

#### generates snippets for all providers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snippets = deploy_snippets()
expect(snippets.len()).to_equal(3)
expect(snippets[0].provider).to_equal("claude")
expect(snippets[1].provider).to_equal("codex")
expect(snippets[2].provider).to_equal("gemini")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/spipe_process_harness/spipe_process_harness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SPipe process harness
- provider normalization
- state and event paths
- hook metadata
- prevention gate
- HUD and deploy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
