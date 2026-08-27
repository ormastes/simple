# Spipe Process Harness Specification

> Tests covering SPipe process harness feature, REQ-001: shared provider support, REQ-002: normalized hook envelope, REQ-003: deploy snippets, REQ-004: CLI HUD, REQ-006: prevention gate.

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

- normalizes supported provider names
   - Expected: normalize_provider("Claude") equals `claude`
   - Expected: normalize_provider("Codex") equals `codex`
   - Expected: normalize_provider("Gemini") equals `gemini`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
# @req REQ-002
# @req REQ-003
# @req REQ-004
# @req REQ-006
# @req REQ-SSPEC-SYSTEM
step("normalizes supported provider names")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(normalize_provider("Claude")).to_equal("claude")
expect(normalize_provider("Codex")).to_equal("codex")
expect(normalize_provider("Gemini")).to_equal("gemini")
```

</details>

#### defines hook lifecycle events for each supported provider

- defines hook lifecycle events for each supported provider


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines hook lifecycle events for each supported provider")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(provider_hook_events("claude")).to_contain("PreToolUse")
expect(provider_hook_events("codex")).to_contain("tool_start")
expect(provider_hook_events("gemini")).to_contain("prompt_submit")
```

</details>

### REQ-002: normalized hook envelope

#### preserves provider event session model and raw payload

- preserves provider event session model and raw payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves provider event session model and raw payload")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- renders deploy snippets for all providers
   - Expected: snippets.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders deploy snippets for all providers")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val snippets = deploy_snippets()
expect(snippets.len()).to_equal(3)  # oracle: snippets.len() must equal 3 — authoritative contract constant
expect(snippets[0].path).to_contain(".spipe/hook-deploy/")
expect(snippets[1].path).to_contain(".spipe/hook-deploy/")
expect(snippets[2].path).to_contain(".spipe/hook-deploy/")
```

</details>

### REQ-004: CLI HUD

#### renders all required HUD fields

- renders all required HUD fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders all required HUD fields")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- blocks state without approval
   - Expected: gate_from_state(state, true).allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks state without approval")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val state = render_state("f", "r", "g", false)
expect(gate_from_state(state, true).allowed).to_equal(false)
```

</details>

#### allows approved state

- allows approved state
   - Expected: gate_from_state(state, true).allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows approved state")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val state = render_state("f", "r", "g", true)
expect(gate_from_state(state, true).allowed).to_equal(true)
```

</details>

#### blocks explicit prevention marker

- blocks explicit prevention marker
   - Expected: decision.allowed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks explicit prevention marker")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SPipe process harness feature, REQ-001: shared provider support, REQ-002: normalized hook envelope, REQ-003: deploy snippets, REQ-004: CLI HUD, REQ-006: prevention gate.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4b12d60bc033b177a18dc33bb3debd28e3a6e9b7f6283acf2407094aa505ebc6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b12d60bc033b177a18dc33bb3debd28e3a6e9b7f6283acf2407094aa505ebc6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b12d60bc033b177a18dc33bb3debd28e3a6e9b7f6283acf2407094aa505ebc6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/spipe_process_harness/feature/spipe_process_harness_spec.spl
mirror: doc/06_spec/03_system/app/spipe_process_harness/feature/spipe_process_harness_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/spipe_process_harness/feature/spipe_process_harness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/spipe_process_harness/feature/spipe_process_harness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
