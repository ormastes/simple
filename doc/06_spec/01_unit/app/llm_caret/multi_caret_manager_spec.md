# Multi Caret Manager Specification

> Tests covering LLM Caret multi-process manager reports process truth.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi Caret Manager Specification

## Scenarios

### LLM Caret multi-process manager reports process truth

#### refuses a launch outside its bounded envelope

- A manager without an id, or outside 1..16 capacity, never spawns


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A manager without an id, or outside 1..16 capacity, never spawns")
expect(launch_multi_caret_manager("", [_request("bogus")], 2,
    "", "", "", "", "").reason).to_equal("manager_id_required")
expect(launch_multi_caret_manager("m", [_request("bogus")], 0,
    "", "", "", "", "").reason).to_equal("capacity_out_of_range")
expect(launch_multi_caret_manager("m", [_request("bogus")], 17,
    "", "", "", "", "").reason).to_equal("capacity_out_of_range")
expect(launch_multi_caret_manager("m", [], 2,
    "", "", "", "", "").reason).to_equal("requests_required")
expect(launch_multi_caret_manager("m",
    [_request("bogus"), _request("bogus"), _request("bogus")], 2,
    "", "", "", "", "").reason).to_equal("capacity_exceeded")
```

</details>

#### reports a clean rollback only when nothing was left running

- Every child failed BEFORE spawning, so no process can leak
   - Expected: m.status equals `not_started`
   - Expected: m.reason equals `launch_rolled_back`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Every child failed BEFORE spawning, so no process can leak")
val m = launch_multi_caret_manager("m-2", [_request("bogus")], 2,
    "", "", "", "", "")
expect(m.status).to_equal("not_started")
expect(m.reason).to_equal("launch_rolled_back")
```

</details>

#### reports a rollback that left children running as an error

- A kill that failed on a real pid is a leak, not a clean rollback
   - Expected: stopped.status equals `stop_failed`
   - Expected: stopped.reason equals `stop_incomplete:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A kill that failed on a real pid is a leak, not a clean rollback")
val leaked = _manager_over([AgentProcess(agent_id: "a",
    status: "error", reason: "process_kill_failed", pid: 424242)])
val stopped = stop_multi_caret_manager(leaked)
expect(stopped.status).to_equal("stop_failed")
expect(stopped.reason).to_equal("stop_incomplete:1")
```

</details>

#### distinguishes a partly-dead team from a fully-dead one

- Spawn one real child, pair it with a never-spawned slot, poll
   - Expected: pid > 0 is true
   - Expected: poll_multi_caret_manager(mixed).status equals `degraded`
- Tearing the same team down kills the survivor and reports clean
   - Expected: stopped.status equals `stopped`
   - Expected: stopped.reason equals `processes_stopped`
- With the survivor gone the team is fully exited, not degraded
   - Expected: poll_multi_caret_manager(mixed).status equals `exited`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Spawn one real child, pair it with a never-spawned slot, poll")
val pid = process_spawn_async("/bin/sleep", ["30"])
expect(pid > 0).to_equal(true)
val mixed = _manager_over([
    AgentProcess(agent_id: "alive", status: "started",
        reason: "process_spawned", pid: pid),
    AgentProcess(agent_id: "dead", status: "started",
        reason: "process_spawned", pid: -1)])
expect(poll_multi_caret_manager(mixed).status).to_equal("degraded")

step("Tearing the same team down kills the survivor and reports clean")
val stopped = stop_multi_caret_manager(mixed)
expect(stopped.status).to_equal("stopped")
expect(stopped.reason).to_equal("processes_stopped")

step("With the survivor gone the team is fully exited, not degraded")
expect(poll_multi_caret_manager(mixed).status).to_equal("exited")
```

</details>

#### leaves a manager that is not running untouched by a poll

- Poll an admission failure that never owned a process

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idle = launch_multi_caret_manager("", [_request("bogus")], 2,
    "", "", "", "", "")
expect(poll_multi_caret_manager(idle).status).to_equal("not_started")
```

</details>

#### continues polling a degraded manager until its children are terminal

- Represent a previously degraded team whose last child has exited
- Poll again and publish the fully terminal state
   - Expected: terminal.status equals `exited`
   - Expected: terminal.reason equals `processes_polled`

<details>
<summary>Executable SSpec</summary>

```simple
val team = summarize_agent_team("m-degraded", [
    AgentProcess(agent_id: "former-survivor", status: "not_running",
        reason: "process_exited", pid: -1)])
val degraded = MultiCaretManager(manager_id: "m-degraded",
    status: "degraded", reason: "processes_polled", capacity: 2,
    team: team, terminal_view: build_agent_tmux_embed(team, []))
val terminal = poll_multi_caret_manager(degraded)
expect(terminal.status).to_equal("exited")
expect(terminal.reason).to_equal("processes_polled")
```

</details>

#### stops an empty team without claiming it killed anything

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idle = launch_multi_caret_manager("", [_request("bogus")], 2,
    "", "", "", "", "")
expect(stop_multi_caret_manager(idle).reason).to_equal("no_processes")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/multi_caret_manager_spec.spl` |
| Updated | 2026-09-02 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret multi-process manager reports process truth.
- LLM Caret multi-process manager reports process truth

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db2eead3e91975aae621c43f280baa8f27e70900296ed3456eb39db52aba358d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db2eead3e91975aae621c43f280baa8f27e70900296ed3456eb39db52aba358d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db2eead3e91975aae621c43f280baa8f27e70900296ed3456eb39db52aba358d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **81/100**; blockers: **0**.

SSpec documentization score: 81/100
source: test/01_unit/app/llm_caret/multi_caret_manager_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/multi_caret_manager_spec.md (current)
findings: 11 blockers: 0
  narrative=80 structure=80 oracle=100
  traceability=80 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/multi_caret_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/multi_caret_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/multi_caret_manager_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/llm_caret/multi_caret_manager_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/app/llm_caret/multi_caret_manager_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/01_unit/app/llm_caret/multi_caret_manager_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/01_unit/app/llm_caret/multi_caret_manager_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a launch outside its bounded envelope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/multi_caret_manager_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a clean rollback only when nothing was left running' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/multi_caret_manager_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a rollback that left children running as an error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/multi_caret_manager_spec.spl:70:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'leaves a manager that is not running untouched by a poll' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/multi_caret_manager_spec.spl:75:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'stops an empty team without claiming it killed anything' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
