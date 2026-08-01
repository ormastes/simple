# Claude Full Ink Event Dispatcher

> Checks capture/bubble listener order, propagation, priorities, and dispatch state.

<!-- sdn-diagram:id=dispatcher_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dispatcher_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dispatcher_spec -> std
dispatcher_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dispatcher_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Ink Event Dispatcher

Checks capture/bubble listener order, propagation, priorities, and dispatch state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/dispatcher_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks capture/bubble listener order, propagation, priorities, and dispatch state.

## Scenarios

### Claude full ink event dispatcher

#### collects listeners in capture then bubble order

- Capture is root-first and bubble is target-first
   - Expected: listeners[0].handlerName equals `root:capture`
   - Expected: listeners[1].handlerName equals `parent:capture`
   - Expected: listeners[2].handlerName equals `target:capture`
   - Expected: listeners[3].handlerName equals `target:bubble`
   - Expected: listeners[4].handlerName equals `parent:bubble`
   - Expected: listeners[5].handlerName equals `root:bubble`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture is root-first and bubble is target-first")
val root = DispatchNode(name: "root", parent: -1, capture: true, bubble: true)
val parent = DispatchNode(name: "parent", parent: 0, capture: true, bubble: true)
val target = DispatchNode(name: "target", parent: 1, capture: true, bubble: true)
val nodes = [root, parent, target]
val listeners = collectListeners(2, nodes, TerminalEventState.new("click", true))
expect(listeners[0].handlerName).to_equal("root:capture")
expect(listeners[1].handlerName).to_equal("parent:capture")
expect(listeners[2].handlerName).to_equal("target:capture")
expect(listeners[3].handlerName).to_equal("target:bubble")
expect(listeners[4].handlerName).to_equal("parent:bubble")
expect(listeners[5].handlerName).to_equal("root:bubble")
```

</details>

#### dispatches and restores state

- Dispatch sets target/currentTarget and then clears transient state
   - Expected: dispatcher.dispatch(1, nodes, event) is true
   - Expected: dispatcher.currentEvent equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch sets target/currentTarget and then clears transient state")
val dispatcher = Dispatcher.new()
val root = DispatchNode(name: "root", parent: -1, capture: true, bubble: true)
val target = DispatchNode(name: "target", parent: 0, capture: false, bubble: true)
val nodes = [root, target]
val event = TerminalEventState.new("click", true)
expect(dispatcher.dispatch(1, nodes, event)).to_equal(true)
expect(dispatcher.currentEvent).to_equal("")
expect(preparedTargetNames(collectListeners(1, nodes, TerminalEventState.new("click", true)), TerminalEventState.new("click", true))).to_contain("target")
```

</details>

#### respects propagation controls

- Immediate and node-boundary propagation stop dispatch
   - Expected: processedHandlerNames(listeners, stopped) equals `[]`
   - Expected: processedHandlerNames(listeners, immediate) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Immediate and node-boundary propagation stop dispatch")
val first = DispatchListener(nodeIndex: 1, nodeName: "target", phase: "at_target", handlerName: "a")
val second = DispatchListener(nodeIndex: 1, nodeName: "target", phase: "at_target", handlerName: "b")
val third = DispatchListener(nodeIndex: 0, nodeName: "root", phase: "bubbling", handlerName: "c")
val listeners = [first, second, third]
val stopped = TerminalEventState.new("click", true)
stopped.propagationStopped = true
expect(processedHandlerNames(listeners, stopped)).to_equal([])
val immediate = TerminalEventState.new("click", true)
immediate.immediateStopped = true
expect(processedHandlerNames(listeners, immediate)).to_equal([])
```

</details>

#### maps event priorities and continuous dispatch

- Discrete, continuous, and default priorities match event type
   - Expected: getEventPriority("click") equals `discreteEventPriority()`
   - Expected: getEventPriority("scroll") equals `continuousEventPriority()`
   - Expected: getEventPriority("custom") equals `defaultEventPriority()`
- dispatcher currentUpdatePriority = noEventPriority
   - Expected: dispatcher.resolveEventPriority() equals `continuousEventPriority()`
   - Expected: dispatcher.dispatchContinuous(0, nodes, event) is true
   - Expected: dispatcher.currentUpdatePriority equals `noEventPriority()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Discrete, continuous, and default priorities match event type")
expect(getEventPriority("click")).to_equal(discreteEventPriority())
expect(getEventPriority("scroll")).to_equal(continuousEventPriority())
expect(getEventPriority("custom")).to_equal(defaultEventPriority())
val dispatcher = Dispatcher.new()
dispatcher.currentUpdatePriority = noEventPriority()
dispatcher.currentEvent = "mousemove"
expect(dispatcher.resolveEventPriority()).to_equal(continuousEventPriority())
val target = DispatchNode(name: "target", parent: -1, capture: false, bubble: true)
val nodes = [target]
val event = TerminalEventState.new("resize", false)
expect(dispatcher.dispatchContinuous(0, nodes, event)).to_equal(true)
expect(dispatcher.currentUpdatePriority).to_equal(noEventPriority())
```

</details>

#### exports source-backed constants

- Pin dispatcher contracts
   - Expected: noEventPriority() equals `0`
   - Expected: discreteEventPriority() equals `1`
   - Expected: continuousEventPriority() equals `2`
   - Expected: defaultEventPriority() equals `3`
   - Expected: captureHandlersRootFirst() is true
   - Expected: bubbleHandlersTargetFirst() is true
   - Expected: targetBubbleRunsEvenWhenEventDoesNotBubble() is true
   - Expected: handlerErrorsAreLoggedAndDispatchContinues() is true
   - Expected: eventPhaseResetAfterDispatch() is true
   - Expected: currentTargetClearedAfterDispatch() is true
   - Expected: currentEventRestoredAfterDispatch() is true
   - Expected: dispatcherSourceLinesModeled() equals `233`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin dispatcher contracts")
expect(noEventPriority()).to_equal(0)
expect(discreteEventPriority()).to_equal(1)
expect(continuousEventPriority()).to_equal(2)
expect(defaultEventPriority()).to_equal(3)
expect(captureHandlersRootFirst()).to_equal(true)
expect(bubbleHandlersTargetFirst()).to_equal(true)
expect(targetBubbleRunsEvenWhenEventDoesNotBubble()).to_equal(true)
expect(handlerErrorsAreLoggedAndDispatchContinues()).to_equal(true)
expect(eventPhaseResetAfterDispatch()).to_equal(true)
expect(currentTargetClearedAfterDispatch()).to_equal(true)
expect(currentEventRestoredAfterDispatch()).to_equal(true)
expect(dispatcherSourceLinesModeled()).to_equal(233)
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
