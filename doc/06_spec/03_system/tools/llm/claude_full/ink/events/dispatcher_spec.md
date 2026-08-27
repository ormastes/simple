# Claude Full Ink Event Dispatcher

> Checks capture/bubble listener order, propagation, priorities, and dispatch state.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks capture/bubble listener order, propagation, priorities, and dispatch state.

## Scenarios

### Claude full ink event dispatcher

#### collects listeners in capture then bubble order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects listeners in capture then bubble order
- Capture is root-first and bubble is target-first
   - Expected: listeners[0].handlerName equals `root:capture`
   - Expected: listeners[1].handlerName equals `parent:capture`
   - Expected: listeners[2].handlerName equals `target:capture`
   - Expected: listeners[3].handlerName equals `target:bubble`
   - Expected: listeners[4].handlerName equals `parent:bubble`
   - Expected: listeners[5].handlerName equals `root:bubble`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collects listeners in capture then bubble order")
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

- dispatches and restores state
- Dispatch sets target/currentTarget and then clears transient state
   - Expected: dispatcher.dispatch(1, nodes, event) is true
   - Expected: dispatcher.currentEvent equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches and restores state")
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

- respects propagation controls
- Immediate and node-boundary propagation stop dispatch
   - Expected: processedHandlerNames(listeners, stopped) equals `[]`
   - Expected: processedHandlerNames(listeners, immediate) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("respects propagation controls")
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

- maps event priorities and continuous dispatch
- Discrete, continuous, and default priorities match event type
   - Expected: getEventPriority("click") equals `discreteEventPriority()`
   - Expected: getEventPriority("scroll") equals `continuousEventPriority()`
   - Expected: getEventPriority("custom") equals `defaultEventPriority()`
   - Expected: dispatcher.resolveEventPriority() equals `continuousEventPriority()`
   - Expected: dispatcher.dispatchContinuous(0, nodes, event) is true
   - Expected: dispatcher.currentUpdatePriority equals `noEventPriority()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps event priorities and continuous dispatch")
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

- exports source-backed constants
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

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `28692af8d92bf731945cacb0d378cc307ea88306f673ec855755b8ac6a33d5b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28692af8d92bf731945cacb0d378cc307ea88306f673ec855755b8ac6a33d5b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28692af8d92bf731945cacb0d378cc307ea88306f673ec855755b8ac6a33d5b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/ink/events/dispatcher_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/events/dispatcher_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/events/dispatcher_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/events/dispatcher_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/events/dispatcher_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/ink/events/dispatcher_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects listeners in capture then bubble order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/dispatcher_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches and restores state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/events/dispatcher_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'respects propagation controls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
