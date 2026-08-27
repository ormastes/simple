# Claude Full CoordinatorAgentStatus

> Checks modeled coordinator state, teammate counts, status priority, progress

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CoordinatorAgentStatus

Checks modeled coordinator state, teammate counts, status priority, progress

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/coordinator_agent_status_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modeled coordinator state, teammate counts, status priority, progress
summary, rendering, and source parity helpers.

## Scenarios

### Claude full CoordinatorAgentStatus component

#### models teammate counts and status priority

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models teammate counts and status priority
- Sample state includes running, done, and error agents
   - Expected: coordinatorTeammateCount(state) equals `3`
   - Expected: coordinatorTotalCount(state) equals `4`
   - Expected: coordinatorRunningCount(state) equals `2`
   - Expected: coordinatorDoneCount(state) equals `1`
   - Expected: coordinatorErrorCount(state) equals `1`
   - Expected: coordinatorStatusLabel(state) equals `error`
   - Expected: coordinatorHasErrors(state) is true
   - Expected: coordinatorAllDone(state) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models teammate counts and status priority")
step("Sample state includes running, done, and error agents")
val state = sampleCoordinatorAgentStatus()

expect(coordinatorTeammateCount(state)).to_equal(3)
expect(coordinatorTotalCount(state)).to_equal(4)
expect(coordinatorRunningCount(state)).to_equal(2)
expect(coordinatorDoneCount(state)).to_equal(1)
expect(coordinatorErrorCount(state)).to_equal(1)
expect(coordinatorStatusLabel(state)).to_equal("error")
expect(coordinatorHasErrors(state)).to_equal(true)
expect(coordinatorAllDone(state)).to_equal(false)
```

</details>

#### summarizes aggregate progress

- summarizes aggregate progress
- Progress sums coordinator and teammate steps
   - Expected: coordinatorProgressPercent(state) equals `50`
   - Expected: coordinatorProgressSummary(state) equals `error | teammates 3 | running 2 | done 1 | error 1 | progress 50%`
   - Expected: state.runningCount() equals `2`
   - Expected: state.doneCount() equals `1`
   - Expected: state.errorCount() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("summarizes aggregate progress")
step("Progress sums coordinator and teammate steps")
val state = sampleCoordinatorAgentStatus()

expect(coordinatorProgressPercent(state)).to_equal(50)
expect(coordinatorProgressSummary(state)).to_equal("error | teammates 3 | running 2 | done 1 | error 1 | progress 50%")
expect(state.progressSummary()).to_contain("teammates 3")
expect(state.runningCount()).to_equal(2)
expect(state.doneCount()).to_equal(1)
expect(state.errorCount()).to_equal(1)
```

</details>

#### normalizes sources and statuses

- normalizes sources and statuses
- Aliases collapse to stable UI labels
   - Expected: running.source equals `builtin`
   - Expected: running.status equals `running`
   - Expected: running.progressText() equals `0/0 0%`
   - Expected: done.source equals `user`
   - Expected: done.status equals `done`
   - Expected: failed.source equals `unknown`
   - Expected: failed.status equals `error`
   - Expected: coordinatorSourceBadge("project") equals `[Project]`
   - Expected: coordinatorStatusBadge("failed") equals `[error]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes sources and statuses")
step("Aliases collapse to stable UI labels")
val running = CoordinatorAgent.new("a", "A", " built-in ", "active", 0, 0, "")
val done = CoordinatorAgent.new("b", "B", "USER", "completed", 5, 5, "")
val failed = CoordinatorAgent.new("c", "C", "other", "blocked", 1, 2, "stuck")

expect(running.source).to_equal("builtin")
expect(running.status).to_equal("running")
expect(running.progressText()).to_equal("0/0 0%")
expect(done.source).to_equal("user")
expect(done.status).to_equal("done")
expect(failed.source).to_equal("unknown")
expect(failed.status).to_equal("error")
expect(coordinatorSourceBadge("project")).to_equal("[Project]")
expect(coordinatorStatusBadge("failed")).to_equal("[error]")
```

</details>

#### renders expanded and collapsed rows

- renders expanded and collapsed rows
- Expanded render includes coordinator and teammate rows
- Collapsed render keeps only the coordinator row
   - Expected: collapsedOutput does not contain `teammate QA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders expanded and collapsed rows")
step("Expanded render includes coordinator and teammate rows")
val expanded = sampleCoordinatorAgentStatus()
val output = renderCoordinatorAgentStatus(expanded)

expect(output).to_contain("Coordinator agents | error")
expect(output).to_contain("updated 12:30")
expect(output).to_contain("coordinator Coordinator [Project] [running] 3/5 60%")
expect(output).to_contain("teammate QA [User] [running] 1/4 25%")
expect(output).to_contain("teammate Docs [Built-in] [done] 2/2 100%")
expect(output).to_contain("Needs rebase")

step("Collapsed render keeps only the coordinator row")
val collapsed = CoordinatorAgentStatusState.new(expanded.coordinator, expanded.teammates, "", "", false)
val collapsedOutput = collapsed.render()
expect(collapsedOutput).to_contain("Coordinator | error")
expect(collapsedOutput).to_contain("coordinator Coordinator")
expect(collapsedOutput.contains("teammate QA")).to_equal(false)
```

</details>

#### reports all-done state without errors

- reports all-done state without errors
- Done wins when every agent is complete
   - Expected: coordinatorAllDone(state) is true
   - Expected: coordinatorStatusLabel(state) equals `done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports all-done state without errors")
step("Done wins when every agent is complete")
val state = CoordinatorAgentStatusState.new(
    CoordinatorAgent.new("coord", "Coordinator", "project", "done", 1, 1, ""),
    [CoordinatorAgent.new("docs", "Docs", "builtin", "done", 2, 2, "")],
    "Done lane",
    "",
    true
)

expect(coordinatorAllDone(state)).to_equal(true)
expect(coordinatorStatusLabel(state)).to_equal("done")
expect(coordinatorProgressSummary(state)).to_contain("progress 100%")
```

</details>

#### exports source helper parity

- exports source helper parity
- Source helper constants stay pinned
   - Expected: coordinatorAgentStatusModeledSourceFile() equals `src/components/CoordinatorAgentStatus.tsx`
   - Expected: coordinatorAgentStatusModeledSourceHelper() equals `getCoordinatorAgentStatus`
   - Expected: coordinatorAgentStatusModeledCountsHelper() equals `countCoordinatorAgentsByStatus`
   - Expected: coordinatorAgentStatusModeledProgressHelper() equals `formatCoordinatorProgress`
   - Expected: coordinatorAgentStatusModeledSourceLines() equals `272`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source helper parity")
step("Source helper constants stay pinned")
expect(coordinatorSourceOptions()).to_contain("project")
expect(coordinatorSourceOptions()).to_contain("user")
expect(coordinatorSourceOptions()).to_contain("builtin")
expect(coordinatorSourceOptions()).to_contain("unknown")
expect(coordinatorAgentStatusModeledSourceFile()).to_equal("src/components/CoordinatorAgentStatus.tsx")
expect(coordinatorAgentStatusModeledSourceHelper()).to_equal("getCoordinatorAgentStatus")
expect(coordinatorAgentStatusModeledCountsHelper()).to_equal("countCoordinatorAgentsByStatus")
expect(coordinatorAgentStatusModeledProgressHelper()).to_equal("formatCoordinatorProgress")
expect(coordinatorAgentStatusModeledSourceLines()).to_equal(272)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eeacc13aceacd6a12953c47763df2de846785b72fec65d5429484462427c6ff6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eeacc13aceacd6a12953c47763df2de846785b72fec65d5429484462427c6ff6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eeacc13aceacd6a12953c47763df2de846785b72fec65d5429484462427c6ff6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/coordinator_agent_status_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/coordinator_agent_status_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/coordinator_agent_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/coordinator_agent_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/coordinator_agent_status_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/coordinator_agent_status_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models teammate counts and status priority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/coordinator_agent_status_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'summarizes aggregate progress' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/coordinator_agent_status_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes sources and statuses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
