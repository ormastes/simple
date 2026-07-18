# Claude Full useTasksV2

> Checks shared task store subscription, hide, polling, and collapse behavior.

<!-- sdn-diagram:id=useTasksV2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=useTasksV2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

useTasksV2_spec -> std
useTasksV2_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=useTasksV2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks shared task store subscription, hide, polling, and collapse behavior.

## Scenarios

### Claude full useTasksV2

#### subscribes lazily and stops on last unsubscribe

- Store starts on first subscriber and stops at zero
- store subscribe
   - Expected: store.started is true
   - Expected: store.subscriberCount equals `1`
- store unsubscribe
   - Expected: store.started is false
   - Expected: store.subscriberCount equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store starts on first subscriber and stops at zero")
val store = TasksV2Store.new()
store.subscribe()
expect(store.started).to_equal(true)
expect(store.subscriberCount).to_equal(1)
store.unsubscribe()
expect(store.started).to_equal(false)
expect(store.subscriberCount).to_equal(0)
```

</details>

#### fetches visible tasks and schedules timers

- Internal tasks are filtered and incomplete tasks poll
- store fetch
   - Expected: store.watcherActive is true
   - Expected: store.tasks.len() equals `1`
   - Expected: store.hidden is false
   - Expected: store.pollTimerActive is true
   - Expected: store.hideTimerActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### hides empty and completed task lists

- Empty lists hide immediately; completed lists hide after timer fires
- emptyStore fetch
- completedStore fetch
   - Expected: completedStore.hideTimerActive is true
- completedStore onHideTimerFired
   - Expected: completedStore.hidden is true
   - Expected: completedStore.tasks equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### keeps hide timer safe across task-list changes

- Scheduled hide does not reset a different task list
- store fetch
- store onHideTimerFired
   - Expected: store.hidden is false
   - Expected: store.tasks.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Scheduled hide does not reset a different task list")
val store = TasksV2Store.new()
store.fetch("old", "/tmp/old", [TaskV2.new("1", "completed", false)], true)
store.onHideTimerFired("old", "new", [TaskV2.new("1", "completed", false)])
expect(store.hidden).to_equal(false)
expect(store.tasks.len()).to_equal(1)
```

</details>

#### exports helpers and constants

- Pin hook enablement, collapse, and timing behavior
   - Expected: filterVisibleTasks([TaskV2.new("i", "completed", true), TaskV2.new("v", "completed", false)]).len() equals `1`
   - Expected: hasIncompleteTasks([TaskV2.new("v", "open", false)]) is true
   - Expected: allStillCompleted([TaskV2.new("v", "completed", false)]) is true
   - Expected: useTasksV2Enabled(true, true, false) is false
   - Expected: useTasksV2Enabled(true, true, true) is true
   - Expected: useTasksV2WithCollapseEffect(true, "tasks") equals `none`
   - Expected: hideDelayMs() equals `5000`
   - Expected: debounceMs() equals `50`
   - Expected: fallbackPollMs() equals `5000`
   - Expected: singletonStoreSharedByHooks() is true
   - Expected: snapshotStableBetweenUpdates() is true
   - Expected: firstFetchRunsPostCommit() is true
   - Expected: fileWatcherRetriesSameDirIfMissing() is true
   - Expected: pollOnlyWhenIncompleteTasksExist() is true
   - Expected: hiddenWhenTaskListEmpty() is true
   - Expected: completedTasksHideAfterDelay() is true
   - Expected: internalTasksFiltered() is true
   - Expected: noopSubscribeStableWhenDisabled() is true
   - Expected: collapseEffectRunsFromOneAlwaysMountedComponent() is true
   - Expected: tasksV2StoreSourceLinesModeled() equals `240`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin hook enablement, collapse, and timing behavior")
expect(filterVisibleTasks([TaskV2.new("i", "completed", true), TaskV2.new("v", "completed", false)]).len()).to_equal(1)
expect(hasIncompleteTasks([TaskV2.new("v", "open", false)])).to_equal(true)
expect(allStillCompleted([TaskV2.new("v", "completed", false)])).to_equal(true)
expect(useTasksV2Enabled(true, true, false)).to_equal(false)
expect(useTasksV2Enabled(true, true, true)).to_equal(true)
expect(useTasksV2WithCollapseEffect(true, "tasks")).to_equal("none")
expect(hideDelayMs()).to_equal(5000)
expect(debounceMs()).to_equal(50)
expect(fallbackPollMs()).to_equal(5000)
expect(singletonStoreSharedByHooks()).to_equal(true)
expect(snapshotStableBetweenUpdates()).to_equal(true)
expect(firstFetchRunsPostCommit()).to_equal(true)
expect(fileWatcherRetriesSameDirIfMissing()).to_equal(true)
expect(pollOnlyWhenIncompleteTasksExist()).to_equal(true)
expect(hiddenWhenTaskListEmpty()).to_equal(true)
expect(completedTasksHideAfterDelay()).to_equal(true)
expect(internalTasksFiltered()).to_equal(true)
expect(noopSubscribeStableWhenDisabled()).to_equal(true)
expect(collapseEffectRunsFromOneAlwaysMountedComponent()).to_equal(true)
expect(tasksV2StoreSourceLinesModeled()).to_equal(240)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
