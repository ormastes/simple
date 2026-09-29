# Llm Caret Multi Manager Specification

> Tests covering bounded parent-owned multi-Caret manager.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Caret Multi Manager Specification

## Scenarios

### bounded parent-owned multi-Caret manager

#### launches four provider wrappers into four derived terminal panes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- launches four provider wrappers into four derived terminal panes
- Build one bounded parent-owned batch
   - Expected: manager.status equals `running`
   - Expected: manager.team.processes.len() equals `4`
   - Expected: manager.terminal_view.session.windows[0].panes.len() equals `4`
- Poll through the parent and perform one terminal cleanup
   - Expected: stopped.status equals `stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("launches four provider wrappers into four derived terminal panes")
step("Build one bounded parent-owned batch")
val requests = [backend_request("claude_cli", "claude"),
    backend_request("codex", "codex"), backend_request("gemini", "gemini"),
    backend_request("kimi", "kimi")]
val manager = launch_multi_caret_manager("system-team", requests, 4,
    "/bin/echo", "/bin/echo", "/bin/echo", "/bin/echo", "")
expect(manager.status).to_equal("running")
expect(manager.team.processes.len()).to_equal(4)
expect(manager.terminal_view.session.windows[0].panes.len()).to_equal(4)
step("Poll through the parent and perform one terminal cleanup")
val polled = poll_multi_caret_manager(manager)
val stopped = stop_multi_caret_manager(polled)
expect(stopped.status).to_equal("stopped")
```

</details>

#### rejects an over-capacity batch before spawning any process

- rejects an over-capacity batch before spawning any process
- Submit two requests to a one-slot manager
   - Expected: manager.status equals `not_started`
   - Expected: manager.reason equals `capacity_exceeded`
   - Expected: manager.team.processes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an over-capacity batch before spawning any process")
step("Submit two requests to a one-slot manager")
val requests = [backend_request("claude_cli", "claude"),
    backend_request("codex", "codex")]
val manager = launch_multi_caret_manager("bounded-team", requests, 1,
    "/bin/echo", "/bin/echo", "", "", "")
expect(manager.status).to_equal("not_started")
expect(manager.reason).to_equal("capacity_exceeded")
expect(manager.team.processes.len()).to_equal(0)
```

</details>

#### keeps terminal stop idempotent at the parent boundary

- keeps terminal stop idempotent at the parent boundary
- Stop an unstarted manager twice
   - Expected: stopped_again.status equals `stopped`
   - Expected: stopped_again.reason equals `no_processes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps terminal stop idempotent at the parent boundary")
step("Stop an unstarted manager twice")
val manager = launch_multi_caret_manager("empty-team", [], 4,
    "", "", "", "", "")
val stopped = stop_multi_caret_manager(manager)
val stopped_again = stop_multi_caret_manager(stopped)
expect(stopped_again.status).to_equal("stopped")
expect(stopped_again.reason).to_equal("no_processes")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/llm_caret_multi_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bounded parent-owned multi-Caret manager.
- bounded parent-owned multi-Caret manager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d74e8ee966cbec1a7b1935ffc7f58a4fb3838510bfb072fba488036740e4aa9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d74e8ee966cbec1a7b1935ffc7f58a4fb3838510bfb072fba488036740e4aa9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d74e8ee966cbec1a7b1935ffc7f58a4fb3838510bfb072fba488036740e4aa9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/llm_caret_multi_manager_spec.spl
mirror: doc/06_spec/03_system/llm_caret_multi_manager_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/llm_caret_multi_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/llm_caret_multi_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/llm_caret_multi_manager_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/llm_caret_multi_manager_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/llm_caret_multi_manager_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'launches four provider wrappers into four derived terminal panes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/llm_caret_multi_manager_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an over-capacity batch before spawning any process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/llm_caret_multi_manager_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps terminal stop idempotent at the parent boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
