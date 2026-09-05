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
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spipe Process Harness Specification

## Scenarios

### SPipe process harness feature

### REQ-001: shared provider support

#### normalizes supported provider names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_provider("Claude")).to_equal("claude")
expect(normalize_provider("Codex")).to_equal("codex")
expect(normalize_provider("Gemini")).to_equal("gemini")
```

</details>

#### defines hook lifecycle events for each supported provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_hook_events("claude")).to_contain("PreToolUse")
expect(provider_hook_events("codex")).to_contain("tool_start")
expect(provider_hook_events("gemini")).to_contain("prompt_submit")
```

</details>

### REQ-002: normalized hook envelope

#### preserves provider event session model and raw payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = hook_jsonl("Claude", "SessionStart", "sid", "sonnet", "{\"ok\":true}")
expect(line).to_contain("\"provider\":\"claude\"")
expect(line).to_contain("\"event\":\"SessionStart\"")
expect(line).to_contain("\"session_id\":\"sid\"")
expect(line).to_contain("\"model\":\"sonnet\"")
expect(line).to_contain("\"raw\"")
```

</details>

### REQ-003: deploy snippets

#### renders deploy snippets for all providers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snippets = deploy_snippets()
expect(snippets.len()).to_equal(3)
expect(snippets[0].path).to_contain(".spipe/hook-deploy/")
expect(snippets[1].path).to_contain(".spipe/hook-deploy/")
expect(snippets[2].path).to_contain(".spipe/hook-deploy/")
```

</details>

### REQ-004: CLI HUD

#### renders all required HUD fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hud = render_hud(HudSnapshot(model: "m", jj_worktree: "w", commit_id: "c", hours_remaining: "h", week_remaining: "wk", goal: "g"))
expect(hud).to_contain("model=m")
expect(hud).to_contain("jj=w")
expect(hud).to_contain("commit=c")
expect(hud).to_contain("hr=h")
expect(hud).to_contain("week=wk")
expect(hud).to_contain("goal=g")
```

</details>

### REQ-006: prevention gate

#### blocks state without approval

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = render_state("f", "r", "g", false)
expect(gate_from_state(state, true).allowed).to_equal(false)
```

</details>

#### allows approved state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = render_state("f", "r", "g", true)
expect(gate_from_state(state, true).allowed).to_equal(true)
```

</details>

#### blocks explicit prevention marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = gate_from_state("User Approved: true\nPrevent: block\n", true)
expect(decision.allowed).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/spipe_process_harness/feature/spipe_process_harness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SPipe process harness feature
- REQ-001: shared provider support
- REQ-002: normalized hook envelope
- REQ-003: deploy snippets
- REQ-004: CLI HUD
- REQ-006: prevention gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
