# spipe_process_harness_spec

> Tests for app.spipe_process_harness and std.nogc_async_mut.spipe_process_harness.

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
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spipe_process_harness_spec

Tests for app.spipe_process_harness and std.nogc_async_mut.spipe_process_harness.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spipe_process_harness/spipe_process_harness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for app.spipe_process_harness and std.nogc_async_mut.spipe_process_harness.

Covers provider normalization, gate semantics, HUD rendering, deploy snippets,
hook path helpers, and event JSONL formatting.

## Scenarios

### SPipe Process Harness

### normalize_provider

#### normalizes claude

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = normalize_provider("claude")
expect(p).to_equal("claude")
```

</details>

#### normalizes Claude (capitalized)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = normalize_provider("Claude")
expect(p).to_equal("claude")
```

</details>

#### normalizes codex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = normalize_provider("codex")
expect(p).to_equal("codex")
```

</details>

#### normalizes openai as codex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = normalize_provider("openai")
expect(p).to_equal("codex")
```

</details>

#### normalizes gpt as codex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = normalize_provider("gpt-4o")
expect(p).to_equal("codex")
```

</details>

#### normalizes gemini

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = normalize_provider("gemini")
expect(p).to_equal("gemini")
```

</details>

#### normalizes google as gemini

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = normalize_provider("google")
expect(p).to_equal("gemini")
```

</details>

#### returns unknown for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = normalize_provider("")
expect(p).to_equal("unknown")
```

</details>

#### passes through unknown provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = normalize_provider("llama")
expect(p).to_equal("llama")
```

</details>

### state_path and event_log_path

#### state_path uses feature name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = state_path("my-feature")
expect(path).to_equal(".spipe/my-feature/state.md")
```

</details>

#### state_path defaults when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = state_path("")
expect(path).to_equal(".spipe/spipe-process-harness/state.md")
```

</details>

#### event_log_path uses feature name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = event_log_path("my-feature")
expect(path).to_equal(".spipe/my-feature/events.jsonl")
```

</details>

### gate_from_state

#### blocks on empty state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = gate_from_state("", false)
expect(gate.allowed == false).to_equal(true)
```

</details>

#### blocks on empty state with exit code 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = gate_from_state("", false)
expect(gate.exit_code).to_equal(2)
```

</details>

#### allows approved state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = make_approved_state()
val gate = gate_from_state(state, true)
expect(gate.allowed).to_equal(true)
```

</details>

#### blocks when approval required but missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = make_unapproved_state()
val gate = gate_from_state(state, true)
expect(gate.allowed == false).to_equal(true)
```

</details>

#### allows when approval not required even without approval marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = make_unapproved_state()
val gate = gate_from_state(state, false)
expect(gate.allowed).to_equal(true)
```

</details>

#### blocks when Prevent: block in state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = make_blocked_state()
val gate = gate_from_state(state, false)
expect(gate.allowed == false).to_equal(true)
```

</details>

### render_hud

#### contains model name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = make_hud_snapshot()
val hud = render_hud(snap)
expect(hud).to_contain("claude-sonnet-4-6")
```

</details>

#### contains jj worktree

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = make_hud_snapshot()
val hud = render_hud(snap)
expect(hud).to_contain("clean")
```

</details>

#### contains hours remaining

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = make_hud_snapshot()
val hud = render_hud(snap)
expect(hud).to_contain("hr=4")
```

</details>

#### contains goal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = make_hud_snapshot()
val hud = render_hud(snap)
expect(hud).to_contain("ship harness")
```

</details>

### deploy_snippets

#### returns 3 snippets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snippets = deploy_snippets()
expect(snippets.len()).to_equal(3)
```

</details>

#### first snippet is for claude

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snippets = deploy_snippets()
expect(snippets[0].provider).to_equal("claude")
```

</details>

#### second snippet is for codex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snippets = deploy_snippets()
expect(snippets[1].provider).to_equal("codex")
```

</details>

#### third snippet is for gemini

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snippets = deploy_snippets()
expect(snippets[2].provider).to_equal("gemini")
```

</details>

#### claude snippet path contains claude-settings-hooks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snippets = deploy_snippets()
expect(snippets[0].path).to_contain("claude-settings-hooks")
```

</details>

### provider_hook_events

#### claude has 9 events

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = provider_hook_events("claude")
expect(events.len()).to_equal(9)
```

</details>

#### codex has 5 events

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = provider_hook_events("codex")
expect(events.len()).to_equal(5)
```

</details>

#### gemini has 5 events

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = provider_hook_events("gemini")
expect(events.len()).to_equal(5)
```

</details>

#### claude events contain PreToolUse

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = provider_hook_events("claude")
expect(events[0]).to_equal("PreToolUse")
```

</details>

#### codex events contain session_start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val events = provider_hook_events("codex")
expect(events[0]).to_equal("session_start")
```

</details>

### hook_command

#### returns bin/simple command for claude

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = hook_command("claude")
expect(cmd).to_contain("bin/simple")
```

</details>

#### includes provider name in command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = hook_command("gemini")
expect(cmd).to_contain("gemini")
```

</details>

### hook_jsonl

#### produces valid json with provider field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val j = hook_jsonl("claude", "PreToolUse", "sess-1", "sonnet", "{}")
expect(j).to_contain("\"provider\":\"claude\"")
```

</details>

#### includes event field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val j = hook_jsonl("codex", "tool_start", "sess-2", "gpt-4o", "{}")
expect(j).to_contain("\"event\":\"tool_start\"")
```

</details>

#### includes type field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val j = hook_jsonl("gemini", "session_start", "sess-3", "gemini-pro", "{}")
expect(j).to_contain("\"type\":\"spipe_hook\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
