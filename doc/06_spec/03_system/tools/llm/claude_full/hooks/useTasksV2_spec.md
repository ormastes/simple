# Claude Full useTasksV2

> Focused Tasks V2 owner behavior with scoped hidden-state evidence for
> `REQ-LLM-CARET-HIDDEN-008`.

| Field | Value |
|---|---|
| Source | `test/03_system/tools/llm/claude_full/hooks/useTasksV2_spec.spl` |
| Executable scenarios | 11 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirement | `REQ-LLM-CARET-HIDDEN-008`, scoped only to hidden empty/completed lists, the disabled no-op hook, and hidden-view collapse |

## Scope and Claim Boundary

This focused manual mirrors Tasks V2 store subscription, visibility, timer, and
helper behavior from `useTasksV2.spl`. The shared-store scenario exercises two
aliases and subscribers against the exported store model; it does not claim
that this pure-Simple owner exposes a production React hook object. The
aggregate feature-gate registry owns the exhaustive gate-input matrix. This
manual does not claim shipped CLI/TUI reachability, live process behavior, or
runtime execution.

Only the empty/completed hiding, disabled no-op hook, and hidden tasks-view
collapse scenarios fulfill `REQ-LLM-CARET-HIDDEN-008`. The other eight
scenarios are supporting hook/store parts-bin evidence.

## Hook Model Helper Contract

`TasksV2HookEnvironment.new()` owns one `TasksV2Store`.
`createHook(enabled)` returns a `TasksV2HookModel` that references that shared
store, so independently created enabled hooks subscribe to and observe the same
updates.

For an enabled model, `commit(...)` marks the hook committed, subscribes it
exactly once before its first fetch, and publishes that fetch through the
shared store. `fetchAfterCommit(...)` called before commit records the rejected
early fetch without mutating the store; after commit it publishes and increments
the hook fetch count. `unmount()` releases only that hook's subscription. A
disabled model leaves commit, subscription, fetch, notification, and task state
untouched.

`snapshotRevision()` exposes the shared store revision. Repeated reads remain
stable until a fetch changes the visible task list or hidden state; a published
change advances the revision.

## Unresolved Source-Sentinel Debt

The authoritative file matrix row
`doc/03_plan/trace/llm_caret_claude_cli_full_parity_file_matrix.tsv:791`
sets the upstream and target line count to **250**. The obsolete owner helper
that returned **240** has now been removed rather than accepted as parity.
The executable spec does not invent a replacement modeled line count and does
not treat the matrix as current PASS evidence; regeneration still requires a
pinned upstream source.

## Scenarios

### Supporting hook and store lifecycle parts-bin behavior

#### should subscribe lazily and stop on last unsubscribe

- Store starts on first subscriber and stops at zero

<details>
<summary>Executable SSpec</summary>

```simple
it "should subscribe lazily and stop on last unsubscribe":
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

- Two hook subscribers observe the same singleton store update

<details>
<summary>Executable SSpec</summary>

```simple
it "should share one store across hook subscribers":
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

- Snapshot revision stays stable until a fetch publishes new tasks

<details>
<summary>Executable SSpec</summary>

```simple
it "should keep snapshots stable between store updates":
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

- Internal tasks are filtered and incomplete tasks poll

<details>
<summary>Executable SSpec</summary>

```simple
it "should fetch visible tasks and schedule timers":
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

- Empty lists hide immediately; completed lists hide after timer fires

<details>
<summary>Executable SSpec</summary>

```simple
it "should hide empty and completed task lists":
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

### Supporting timer, watcher, and post-commit parts-bin behavior

#### should keep the hide timer safe across task-list changes

- Scheduled hide does not reset a different task list

<details>
<summary>Executable SSpec</summary>

```simple
it "should keep the hide timer safe across task-list changes":
    step("Scheduled hide does not reset a different task list")
    val store = TasksV2Store.new()
    store.fetch("old", "/tmp/old", [TaskV2.new("1", "completed", false)], true)
    store.onHideTimerFired("old", "new", [TaskV2.new("1", "completed", false)])
    expect(store.hidden).to_equal(false)
    expect(store.tasks.len()).to_equal(1)
```

</details>

#### should retry failed watches and debounce task changes

- A failed same-directory watch retries and changes arm debounce

<details>
<summary>Executable SSpec</summary>

```simple
it "should retry failed watches and debounce task changes":
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

- Subscription starts before the first fetch publishes an update

<details>
<summary>Executable SSpec</summary>

```simple
it "should fetch first tasks after subscription commit":
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

- Disabled Tasks V2 selects the stable no-op subscription

<details>
<summary>Executable SSpec</summary>

```simple
it "should leave subscription state untouched when disabled":
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

- The collapse owner closes only a hidden tasks view

<details>
<summary>Executable SSpec</summary>

```simple
it "should collapse tasks from one always-mounted owner":
    step("The collapse owner closes only a hidden tasks view")
    expect(useTasksV2WithCollapseEffect(true, "tasks")).to_equal("none")
    expect(useTasksV2WithCollapseEffect(false, "tasks")).to_equal("tasks")
    expect(useTasksV2WithCollapseEffect(true, "agents")).to_equal("agents")
```

</details>

### Supporting helpers and constants parts-bin behavior

#### should export focused helpers and constants

- Pin hook enablement, collapse, and timing behavior

<details>
<summary>Executable SSpec</summary>

```simple
it "should export focused helpers and constants":
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

## Execution Status

The executable spec and this mirrored manual were updated statically. No
runtime was invoked, 0 scenarios were executed, and no PASS is claimed.
