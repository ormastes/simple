# Claude Full Stop Task

> Checks stopTask validation, kill, local shell notification suppression, and errors.

<!-- sdn-diagram:id=stopTask_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stopTask_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stopTask_spec -> std
stopTask_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stopTask_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Stop Task

Checks stopTask validation, kill, local shell notification suppression, and errors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tasks/stopTask_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks stopTask validation, kill, local shell notification suppression, and errors.

## Scenarios

### Claude full stopTask

#### should report not found errors

- Stop missing task
   - Expected: result.error.name equals `StopTaskError`
   - Expected: result.error.code equals `not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stop missing task")
val context = StopTaskContext.new([], ["bash"])
val result = stopTask("missing", context)
expect(result.error.name).to_equal("StopTaskError")
expect(result.error.code).to_equal("not_found")
expect(result.error.message).to_contain("No task found")
```

</details>

#### should report not running errors

- Stop completed task
   - Expected: result.error.code equals `not_running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stop completed task")
val context = StopTaskContext.new([TaskState.new("t1", "bash", "completed", "echo hi", "desc")], ["bash"])
val result = stopTask("t1", context)
expect(result.error.code).to_equal("not_running")
expect(result.error.message).to_contain("status: completed")
```

</details>

#### should report unsupported task types

- Stop unsupported task
   - Expected: result.error.code equals `unsupported_type`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stop unsupported task")
val context = StopTaskContext.new([TaskState.new("t1", "agent", "running", "", "agent work")], ["bash"])
val result = stopTask("t1", context)
expect(result.error.code).to_equal("unsupported_type")
expect(result.error.message).to_contain("agent")
```

</details>

#### should kill local shell task and emit sdk termination

- Stop running bash task
   - Expected: result.taskId equals `t1`
   - Expected: result.taskType equals `bash`
   - Expected: result.command equals `npm test`
   - Expected: result.killedTaskIds equals `["t1"]`
   - Expected: result.notified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Stop notified bash task
- var task = TaskState new
   - Expected: result.command equals `sleep 1`
   - Expected: result.sdkEvents.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stop notified bash task")
var task = TaskState.new("t1", "local_shell", "running", "sleep 1", "sleep")
task.notified = true
val context = StopTaskContext.new([task], ["local_shell"])
val result = stopTask("t1", context)
expect(result.command).to_equal("sleep 1")
expect(result.sdkEvents.len()).to_equal(0)
```

</details>

#### should return description for non-shell tasks

- Stop agent task
   - Expected: result.taskType equals `agent`
   - Expected: result.command equals `summarize`
   - Expected: result.killedTaskIds equals `["a1"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stop agent task")
val context = StopTaskContext.new([TaskState.new("a1", "agent", "running", "", "summarize")], ["agent"])
val result = stopTask("a1", context)
expect(result.taskType).to_equal("agent")
expect(result.command).to_equal("summarize")
expect(result.killedTaskIds).to_equal(["a1"])
```

</details>

#### should expose source-backed helpers

- Pin helper behavior
   - Expected: isLocalShellTask(TaskState.new("t", "bash", "running", "c", "d")) is true
   - Expected: containsTextStopTask(["a", "b"], "b") is true
   - Expected: stopTaskSourceLinesModeled() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin helper behavior")
expect(isLocalShellTask(TaskState.new("t", "bash", "running", "c", "d"))).to_equal(true)
expect(containsTextStopTask(["a", "b"], "b")).to_equal(true)
expect(stopTaskSourceLinesModeled()).to_equal(100)
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
