# Claude Full Stop Task

> Purpose: should report not found errors

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Stop Task

Purpose: should report not found errors

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should report not found errors
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Stop Task

Checks stopTask validation, kill, local shell notification suppression, and errors.

## Scenarios

### Claude full stopTask

#### should report not found errors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should report not found errors
- Verify: should report not found errors
- Stop missing task
   - Expected: result.error.name equals `StopTaskError`
   - Expected: result.error.code equals `not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report not found errors")
step("Verify: should report not found errors")
# @req: REQ-TOOLS-Stop-001
step("Stop missing task")
val context = StopTaskContext.new([], ["bash"])
val result = stopTask("missing", context)
expect(result.error.name).to_equal("StopTaskError")
expect(result.error.code).to_equal("not_found")
expect(result.error.message).to_contain("No task found")
```

</details>

#### should report not running errors

- should report not running errors
- Verify: should report not running errors
- Stop completed task
   - Expected: result.error.code equals `not_running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report not running errors")
step("Verify: should report not running errors")
# @req: REQ-TOOLS-Stop-001
step("Stop completed task")
val context = StopTaskContext.new([TaskState.new("t1", "bash", "completed", "echo hi", "desc")], ["bash"])
val result = stopTask("t1", context)
expect(result.error.code).to_equal("not_running")
expect(result.error.message).to_contain("status: completed")
```

</details>

#### should report unsupported task types

- should report unsupported task types
- Verify: should report unsupported task types
- Stop unsupported task
   - Expected: result.error.code equals `unsupported_type`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report unsupported task types")
step("Verify: should report unsupported task types")
# @req: REQ-TOOLS-Stop-001
step("Stop unsupported task")
val context = StopTaskContext.new([TaskState.new("t1", "agent", "running", "", "agent work")], ["bash"])
val result = stopTask("t1", context)
expect(result.error.code).to_equal("unsupported_type")
expect(result.error.message).to_contain("agent")
```

</details>

#### should kill local shell task and emit sdk termination

- should kill local shell task and emit sdk termination
- Verify: should kill local shell task and emit sdk termination
- Stop running bash task
   - Expected: result.taskId equals `t1`
   - Expected: result.taskType equals `bash`
   - Expected: result.command equals `npm test`
   - Expected: result.killedTaskIds equals `["t1"]`
   - Expected: result.notified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should kill local shell task and emit sdk termination")
step("Verify: should kill local shell task and emit sdk termination")
# @req: REQ-TOOLS-Stop-001
step("Stop running bash task")
val task = TaskState.new("t1", "bash", "running", "npm test", "run tests")
val context = StopTaskContext.new([task], ["bash"])
val result = stopTask("t1", context)
expect(result.taskId).to_equal("t1")
expect(result.taskType).to_equal("bash")
expect(result.command).to_equal("npm test")
expect(result.killedTaskIds).to_equal(["t1"])
expect(result.notified).to_equal(true)
expect(result.sdkEvents[0]).to_contain("terminated:t1:stopped")
```

</details>

#### should not duplicate sdk event for already notified local shell task

- should not duplicate sdk event for already notified local shell task
- Verify: should not duplicate sdk event for already notified local shell task
- Stop notified bash task
   - Expected: result.command equals `sleep 1`
   - Expected: result.sdkEvents.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should not duplicate sdk event for already notified local shell task")
step("Verify: should not duplicate sdk event for already notified local shell task")
# @req: REQ-TOOLS-Stop-001
step("Stop notified bash task")
var task = TaskState.new("t1", "local_shell", "running", "sleep 1", "sleep")
task.notified = true
val context = StopTaskContext.new([task], ["local_shell"])
val result = stopTask("t1", context)
expect(result.command).to_equal("sleep 1")
expect(result.sdkEvents.len()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should return description for non-shell tasks

- should return description for non-shell tasks
- Verify: should return description for non-shell tasks
- Stop agent task
   - Expected: result.taskType equals `agent`
   - Expected: result.command equals `summarize`
   - Expected: result.killedTaskIds equals `["a1"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return description for non-shell tasks")
step("Verify: should return description for non-shell tasks")
# @req: REQ-TOOLS-Stop-001
step("Stop agent task")
val context = StopTaskContext.new([TaskState.new("a1", "agent", "running", "", "summarize")], ["agent"])
val result = stopTask("a1", context)
expect(result.taskType).to_equal("agent")
expect(result.command).to_equal("summarize")
expect(result.killedTaskIds).to_equal(["a1"])
```

</details>

#### should expose source-backed helpers

- should expose source-backed helpers
- Verify: should expose source-backed helpers
- Pin helper behavior
   - Expected: isLocalShellTask(TaskState.new("t", "bash", "running", "c", "d")) is true
   - Expected: containsTextStopTask(["a", "b"], "b") is true
   - Expected: stopTaskSourceLinesModeled() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed helpers")
step("Verify: should expose source-backed helpers")
# @req: REQ-TOOLS-Stop-001
step("Pin helper behavior")
expect(isLocalShellTask(TaskState.new("t", "bash", "running", "c", "d"))).to_equal(true)
expect(containsTextStopTask(["a", "b"], "b")).to_equal(true)
expect(stopTaskSourceLinesModeled()).to_equal(100)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Stop-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d5568ab84457413bf75fd51265fa60b4a8f5ff7ff55fcf9513fddd6420960b7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d5568ab84457413bf75fd51265fa60b4a8f5ff7ff55fcf9513fddd6420960b7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d5568ab84457413bf75fd51265fa60b4a8f5ff7ff55fcf9513fddd6420960b7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tasks/stopTask_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tasks/stopTask_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tasks/stopTask_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report not found errors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report not found errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report not running errors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report not running errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report unsupported task types' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report unsupported task types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should kill local shell task and emit sdk termination' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not duplicate sdk event for already notified local shell task' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return description for non-shell tasks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
