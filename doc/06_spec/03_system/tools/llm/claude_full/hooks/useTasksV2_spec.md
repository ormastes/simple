# Claude Full useTasksV2

> Checks shared task store subscription, hide, polling, and collapse behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full useTasksV2

Checks shared task store subscription, hide, polling, and collapse behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Checks shared task store subscription, hide, polling, and collapse behavior.

REQ-LLM-CARET-HIDDEN-008 applies only to hiding empty/completed lists, the
disabled no-op hook, and collapsing a hidden tasks view.

Claim boundary: this focused owner spec proves Tasks V2 store, visibility,
timer, and helper behavior from `useTasksV2.spl`. The aggregate feature-gate
registry owns the exhaustive gate-input matrix. This spec does not prove
shipped CLI/TUI reachability or live process behavior.

## Scenarios

### Claude full useTasksV2

### supporting hook and store lifecycle parts-bin behavior

#### should subscribe lazily and stop on last unsubscribe

- should subscribe lazily and stop on last unsubscribe
- Store starts on first subscriber and stops at zero
   - Expected: store.started is true
   - Expected: store.subscriberCount equals `2`
   - Expected: store.started is true
   - Expected: store.subscriberCount equals `1`
   - Expected: store.watcherActive is true
   - Expected: store.debounceTimerActive is true
   - Expected: store.started is false
   - Expected: store.subscriberCount equals `0`
   - Expected: store.watcherActive is false
   - Expected: store.debounceTimerActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-LLM-CARET-HIDDEN-008
step("should subscribe lazily and stop on last unsubscribe")
step("Store starts on first subscriber and stops at zero")
val store = TasksV2Store.new()
store.subscribe()
store.subscribe()
expect(store.started).to_equal(true)
expect(store.subscriberCount).to_equal(2)
store.rewatch("/tmp/tasks", true)
store.debouncedFetch()
store.unsubscribe()
expect(store.started).to_equal(true)
expect(store.subscriberCount).to_equal(1)
expect(store.watcherActive).to_equal(true)
expect(store.debounceTimerActive).to_equal(true)
store.unsubscribe()
expect(store.started).to_equal(false)
expect(store.subscriberCount).to_equal(0)
expect(store.watcherActive).to_equal(false)
expect(store.debounceTimerActive).to_equal(false)
```

</details>

#### should share one store across hook subscribers

- should share one store across hook subscribers
- Two hook subscribers observe the same singleton store update
   - Expected: secondSnapshot.?.len() equals `1`
   - Expected: secondSnapshot.?[0].id equals `shared`
   - Expected: environment.store.subscriberCount equals `2`
   - Expected: environment.store.notifications equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should share one store across hook subscribers")
step("Two hook subscribers observe the same singleton store update")
val environment = TasksV2HookEnvironment.new()
val firstHook = environment.createHook(true)
val secondHook = environment.createHook(true)
firstHook.commit("tasks", "/tmp/tasks", [TaskV2.new("shared", "in_progress", false)], true)
secondHook.commit("tasks", "/tmp/tasks", [TaskV2.new("shared", "in_progress", false)], true)
val secondSnapshot = secondHook.getSnapshot()
expect(secondSnapshot == nil).to_be(false)
expect(secondSnapshot.?.len()).to_equal(1)
expect(secondSnapshot.?[0].id).to_equal("shared")
expect(environment.store.subscriberCount).to_equal(2)
expect(environment.store.notifications).to_equal(2)
firstHook.unmount()
expect(environment.store.started).to_be(true)
secondHook.unmount()
expect(environment.store.started).to_be(false)
```

</details>

#### should keep snapshots stable between store updates

- should keep snapshots stable between store updates
- Snapshot revision stays stable until a fetch publishes new tasks
   - Expected: firstRevision equals `1`
   - Expected: hook.snapshotRevision() equals `firstRevision`
   - Expected: hook.getSnapshot().?[0].id equals `first`
   - Expected: hook.snapshotRevision() equals `firstRevision + 1`
   - Expected: hook.getSnapshot().?[0].id equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep snapshots stable between store updates")
step("Snapshot revision stays stable until a fetch publishes new tasks")
val environment = TasksV2HookEnvironment.new()
val hook = environment.createHook(true)
hook.commit("tasks", "/tmp/tasks", [TaskV2.new("first", "in_progress", false)], true)
val firstRevision = hook.snapshotRevision()
expect(firstRevision).to_equal(1)
expect(hook.snapshotRevision()).to_equal(firstRevision)
expect(hook.getSnapshot().?[0].id).to_equal("first")
hook.fetchAfterCommit("tasks", "/tmp/tasks", [TaskV2.new("second", "in_progress", false)], true)
expect(hook.snapshotRevision()).to_equal(firstRevision + 1)
expect(hook.getSnapshot().?[0].id).to_equal("second")
```

</details>

#### should fetch visible tasks and schedule timers

- should fetch visible tasks and schedule timers
- Internal tasks are filtered and incomplete tasks poll
   - Expected: store.watcherActive is true
   - Expected: store.tasks.len() equals `1`
   - Expected: store.hidden is false
   - Expected: store.pollTimerActive is true
   - Expected: store.hideTimerActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fetch visible tasks and schedule timers")
step("Internal tasks are filtered and incomplete tasks poll")
val store = TasksV2Store.new()
store.fetch("tasks", "/tmp/tasks", [TaskV2.new("1", "completed", true), TaskV2.new("2", "in_progress", false)], true)
expect(store.watcherActive).to_equal(true)
expect(store.tasks.len()).to_equal(1)
expect(store.hidden).to_equal(false)
expect(store.pollTimerActive).to_equal(true)
expect(store.hideTimerActive).to_equal(false)
```

</details>

### REQ-LLM-CARET-HIDDEN-008: hidden empty and completed task lists

#### should hide empty and completed task lists

- should hide empty and completed task lists
- Empty lists hide immediately; completed lists hide after timer fires
   - Expected: completedStore.hideTimerActive is true
   - Expected: completedStore.hidden is true
   - Expected: completedStore.tasks equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should hide empty and completed task lists")
step("Empty lists hide immediately; completed lists hide after timer fires")
val emptyStore = TasksV2Store.new()
emptyStore.fetch("tasks", "/tmp/tasks", [], true)
expect(emptyStore.getSnapshot()).to_be_nil()
val completedStore = TasksV2Store.new()
completedStore.fetch("tasks", "/tmp/tasks", [TaskV2.new("1", "completed", false)], true)
expect(completedStore.hideTimerActive).to_equal(true)
completedStore.onHideTimerFired("tasks", "tasks", [TaskV2.new("1", "completed", false)])
expect(completedStore.hidden).to_equal(true)
expect(completedStore.tasks).to_equal([])
```

</details>

### supporting timer watcher and post-commit parts-bin behavior

#### should keep the hide timer safe across task-list changes

- should keep the hide timer safe across task-list changes
- Scheduled hide does not reset a different task list
   - Expected: store.hidden is false
   - Expected: store.tasks.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the hide timer safe across task-list changes")
step("Scheduled hide does not reset a different task list")
val store = TasksV2Store.new()
store.fetch("old", "/tmp/old", [TaskV2.new("1", "completed", false)], true)
store.onHideTimerFired("old", "new", [TaskV2.new("1", "completed", false)])
expect(store.hidden).to_equal(false)
expect(store.tasks.len()).to_equal(1)
```

</details>

#### should retry failed watches and debounce task changes

- should retry failed watches and debounce task changes
- A failed same-directory watch retries and changes arm debounce
   - Expected: store.watchedDir equals `/tmp/tasks`
   - Expected: store.watcherActive is false
   - Expected: store.watcherActive is true
   - Expected: store.debounceTimerActive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retry failed watches and debounce task changes")
step("A failed same-directory watch retries and changes arm debounce")
val store = TasksV2Store.new()
store.rewatch("/tmp/tasks", false)
expect(store.watchedDir).to_equal("/tmp/tasks")
expect(store.watcherActive).to_equal(false)
store.rewatch("/tmp/tasks", true)
expect(store.watcherActive).to_equal(true)
store.debouncedFetch()
expect(store.debounceTimerActive).to_equal(true)
```

</details>

#### should fetch first tasks after subscription commit

- should fetch first tasks after subscription commit
- Subscription starts before the first fetch publishes an update
   - Expected: hook.fetchesBeforeCommit equals `1`
   - Expected: environment.store.notifications equals `0`
   - Expected: hook.fetchCount equals `1`
   - Expected: environment.store.notifications equals `1`
   - Expected: environment.store.tasks[0].id equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fetch first tasks after subscription commit")
step("Subscription starts before the first fetch publishes an update")
val environment = TasksV2HookEnvironment.new()
val hook = environment.createHook(true)
hook.fetchAfterCommit("tasks", "/tmp/tasks", [TaskV2.new("early", "in_progress", false)], true)
expect(hook.fetchesBeforeCommit).to_equal(1)
expect(environment.store.notifications).to_equal(0)
expect(environment.store.started).to_be(false)
hook.commit("tasks", "/tmp/tasks", [TaskV2.new("first", "in_progress", false)], true)
expect(hook.committed).to_be(true)
expect(hook.subscribed).to_be(true)
expect(hook.subscribedBeforeFirstFetch).to_be(true)
expect(hook.fetchCount).to_equal(1)
expect(environment.store.notifications).to_equal(1)
expect(environment.store.tasks[0].id).to_equal("first")
```

</details>

### REQ-LLM-CARET-HIDDEN-008: disabled and collapsed hidden task states

#### should leave subscription state untouched when disabled

- should leave subscription state untouched when disabled
- Disabled Tasks V2 selects the stable no-op subscription
   - Expected: useTasksV2Enabled(false, false, false) is false
   - Expected: hook.fetchCount equals `0`
   - Expected: environment.store.subscriberCount equals `0`
   - Expected: environment.store.notifications equals `0`
   - Expected: environment.store.tasks.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should leave subscription state untouched when disabled")
step("Disabled Tasks V2 selects the stable no-op subscription")
val environment = TasksV2HookEnvironment.new()
val hook = environment.createHook(false)
expect(useTasksV2Enabled(false, false, false)).to_equal(false)
hook.commit("tasks", "/tmp/tasks", [TaskV2.new("hidden", "in_progress", false)], true)
expect(hook.committed).to_be(false)
expect(hook.subscribed).to_be(false)
expect(hook.fetchCount).to_equal(0)
expect(environment.store.started).to_be(false)
expect(environment.store.subscriberCount).to_equal(0)
expect(environment.store.notifications).to_equal(0)
expect(environment.store.tasks.len()).to_equal(0)
```

</details>

#### should collapse tasks from one always-mounted owner

- should collapse tasks from one always-mounted owner
- The collapse owner closes only a hidden tasks view
   - Expected: useTasksV2WithCollapseEffect(true, "tasks") equals `none`
   - Expected: useTasksV2WithCollapseEffect(false, "tasks") equals `tasks`
   - Expected: useTasksV2WithCollapseEffect(true, "agents") equals `agents`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should collapse tasks from one always-mounted owner")
step("The collapse owner closes only a hidden tasks view")
expect(useTasksV2WithCollapseEffect(true, "tasks")).to_equal("none")
expect(useTasksV2WithCollapseEffect(false, "tasks")).to_equal("tasks")
expect(useTasksV2WithCollapseEffect(true, "agents")).to_equal("agents")
```

</details>

### supporting helper and constant parts-bin behavior

#### should export focused helpers and constants

- should export focused helpers and constants
- Pin hook enablement, collapse, and timing behavior
   - Expected: filterVisibleTasks([TaskV2.new("i", "completed", true), TaskV2.new("v", "completed", false)]).len() equals `1`
   - Expected: hasIncompleteTasks([TaskV2.new("v", "open", false)]) is true
   - Expected: allStillCompleted([TaskV2.new("v", "completed", false)]) is true
   - Expected: useTasksV2Enabled(true, true, false) is false
   - Expected: useTasksV2Enabled(true, true, true) is true
   - Expected: hideDelayMs() equals `5000`
   - Expected: debounceMs() equals `50`
   - Expected: fallbackPollMs() equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should export focused helpers and constants")
step("Pin hook enablement, collapse, and timing behavior")
expect(filterVisibleTasks([TaskV2.new("i", "completed", true), TaskV2.new("v", "completed", false)]).len()).to_equal(1)
expect(hasIncompleteTasks([TaskV2.new("v", "open", false)])).to_equal(true)
expect(allStillCompleted([TaskV2.new("v", "completed", false)])).to_equal(true)
expect(useTasksV2Enabled(true, true, false)).to_equal(false)
expect(useTasksV2Enabled(true, true, true)).to_equal(true)
expect(hideDelayMs()).to_equal(5000)
expect(debounceMs()).to_equal(50)
expect(fallbackPollMs()).to_equal(5000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-HIDDEN-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3d7bc4dc22b900cbd5bae92001183c0e31e317e9d769ad4e726ff80b58ccab14`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d7bc4dc22b900cbd5bae92001183c0e31e317e9d769ad4e726ff80b58ccab14`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d7bc4dc22b900cbd5bae92001183c0e31e317e9d769ad4e726ff80b58ccab14`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should subscribe lazily and stop on last unsubscribe' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should subscribe lazily and stop on last unsubscribe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should share one store across hook subscribers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should share one store across hook subscribers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep snapshots stable between store updates' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep snapshots stable between store updates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fetch visible tasks and schedule timers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should hide empty and completed task lists' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl:114:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the hide timer safe across task-list changes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
