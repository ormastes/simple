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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- refuses a launch outside its bounded envelope
- A manager without an id, or outside 1..16 capacity, never spawns


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a launch outside its bounded envelope")
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

- reports a clean rollback only when nothing was left running
- Every child failed BEFORE spawning, so no process can leak
   - Expected: m.status equals `not_started`
   - Expected: m.reason equals `launch_rolled_back`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a clean rollback only when nothing was left running")
step("Every child failed BEFORE spawning, so no process can leak")
val m = launch_multi_caret_manager("m-2", [_request("bogus")], 2,
    "", "", "", "", "")
expect(m.status).to_equal("not_started")
expect(m.reason).to_equal("launch_rolled_back")
```

</details>

#### reports a rollback that left children running as an error

- reports a rollback that left children running as an error
- A kill that failed on a real pid is a leak, not a clean rollback
   - Expected: stopped.status equals `stop_failed`
   - Expected: stopped.reason equals `stop_incomplete:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a rollback that left children running as an error")
step("A kill that failed on a real pid is a leak, not a clean rollback")
val leaked = _manager_over([AgentProcess(agent_id: "a",
    status: "error", reason: "process_kill_failed", pid: 424242)])
val stopped = stop_multi_caret_manager(leaked)
expect(stopped.status).to_equal("stop_failed")
expect(stopped.reason).to_equal("stop_incomplete:1")
```

</details>

#### distinguishes a partly-dead team from a fully-dead one

- distinguishes a partly-dead team from a fully-dead one
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

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes a partly-dead team from a fully-dead one")
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

- leaves a manager that is not running untouched by a poll
   - Expected: poll_multi_caret_manager(idle).status equals `not_started`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a manager that is not running untouched by a poll")
val idle = launch_multi_caret_manager("", [_request("bogus")], 2,
    "", "", "", "", "")
expect(poll_multi_caret_manager(idle).status).to_equal("not_started")
```

</details>

#### stops an empty team without claiming it killed anything

- stops an empty team without claiming it killed anything
   - Expected: stop_multi_caret_manager(idle).reason equals `no_processes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops an empty team without claiming it killed anything")
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
| Source | `test/unit/app/llm_caret/multi_caret_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret multi-process manager reports process truth.
- LLM Caret multi-process manager reports process truth

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eeab824fb3edaaf1ca46e23202b874a16f9cdb9e3fd4055ab7cb114432b3c29c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eeab824fb3edaaf1ca46e23202b874a16f9cdb9e3fd4055ab7cb114432b3c29c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eeab824fb3edaaf1ca46e23202b874a16f9cdb9e3fd4055ab7cb114432b3c29c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/llm_caret/multi_caret_manager_spec.spl
mirror: doc/06_spec/unit/app/llm_caret/multi_caret_manager_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_caret/multi_caret_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_caret/multi_caret_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_caret/multi_caret_manager_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a launch outside its bounded envelope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/multi_caret_manager_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a clean rollback only when nothing was left running' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/multi_caret_manager_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a rollback that left children running as an error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
