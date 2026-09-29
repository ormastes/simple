# Async Ui Specification

> Tests covering UIEventBus creation, event send and try_recv, send_event helper, render queue batching, stop_event_bus, AsyncReactiveStore, async reactive change notifications, async dirty tracking, AsyncUIState dispatch, AsyncUIState read access, channel close behaviour.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Ui Specification

## Scenarios

### UIEventBus creation

#### creates bus with running flag true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates bus with running flag true
   - Expected: bus.running is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates bus with running flag true")
val bus = new_event_bus()
expect(bus.running).to_equal(true)
```

</details>

#### creates bus with open event channel

- creates bus with open event channel
   - Expected: bus.events.is_closed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates bus with open event channel")
val bus = new_event_bus()
expect(bus.events.is_closed()).to_equal(false)
```

</details>

#### creates bus with open render queue

- creates bus with open render queue
   - Expected: bus.render_queue.is_closed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates bus with open render queue")
val bus = new_event_bus()
expect(bus.render_queue.is_closed()).to_equal(false)
```

</details>

### event send and try_recv

#### sends and receives a KeyPress event

- sends and receives a KeyPress event


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends and receives a KeyPress event")
val bus = new_event_bus()
bus.events.send(UIEvent.KeyPress(key: "j"))
val received = bus.events.try_recv()
assert_not_equal(received, nil)
```

</details>

#### returns nil when no events pending

- returns nil when no events pending
   - Expected: received equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when no events pending")
val bus = new_event_bus()
val received = bus.events.try_recv()
expect(received).to_equal(nil)
```

</details>

#### sends and receives Quit event

- sends and receives Quit event


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends and receives Quit event")
val bus = new_event_bus()
bus.events.send(UIEvent.Quit)
val received = bus.events.try_recv()
assert_not_equal(received, nil)
```

</details>

#### preserves FIFO order

- preserves FIFO order
   - Expected: e4 equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves FIFO order")
val bus = new_event_bus()
bus.events.send(UIEvent.FocusNext)
bus.events.send(UIEvent.FocusPrev)
bus.events.send(UIEvent.Quit)
val e1 = bus.events.try_recv()
val e2 = bus.events.try_recv()
val e3 = bus.events.try_recv()
val e4 = bus.events.try_recv()
assert_not_equal(e1, nil)
assert_not_equal(e2, nil)
assert_not_equal(e3, nil)
expect(e4).to_equal(nil)
```

</details>

### send_event helper

#### pushes event through the bus

- pushes event through the bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes event through the bus")
val bus = new_event_bus()
send_event(bus, UIEvent.FocusNext)
val received = bus.events.try_recv()
assert_not_equal(received, nil)
```

</details>

### render queue batching

#### sends state to render queue

- sends state to render queue


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends state to render queue")
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
bus.render_queue.send(state)
val received = bus.render_queue.try_recv()
assert_not_equal(received, nil)
```

</details>

#### drains all queued renders leaving only latest

- drains all queued renders leaving only latest
   - Expected: empty equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drains all queued renders leaving only latest")
val bus = new_event_bus()
val tree = make_async_test_tree()
val s1 = init_state(tree)
val s2 = update_state(s1, UIEvent.FocusNext)
val s3 = update_state(s2, UIEvent.FocusNext)
# Queue three renders
bus.render_queue.send(s1)
bus.render_queue.send(s2)
bus.render_queue.send(s3)
# Drain to find latest (simulates loop batching)
var latest: UIState? = nil
var has_render = true
while has_render:
    val queued = bus.render_queue.try_recv()
    if queued != nil:
        latest = queued
    else:
        has_render = false
assert_not_equal(latest, nil)
# Queue should now be empty
val empty = bus.render_queue.try_recv()
expect(empty).to_equal(nil)
```

</details>

### stop_event_bus

#### sets running to false

- sets running to false
   - Expected: bus.running is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets running to false")
val bus = new_event_bus()
stop_event_bus(bus)
expect(bus.running).to_equal(false)
```

</details>

#### closes event channel

- closes event channel
   - Expected: bus.events.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes event channel")
val bus = new_event_bus()
stop_event_bus(bus)
expect(bus.events.is_closed()).to_equal(true)
```

</details>

#### closes render queue channel

- closes render queue channel
   - Expected: bus.render_queue.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes render queue channel")
val bus = new_event_bus()
stop_event_bus(bus)
expect(bus.render_queue.is_closed()).to_equal(true)
```

</details>

### AsyncReactiveStore

#### creates empty store

- creates empty store
   - Expected: value equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty store")
val store = new_async_store()
val value = async_get(store, "x")
expect(value).to_equal("")
```

</details>

#### defines and gets a value

- defines and gets a value
   - Expected: value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines and gets a value")
val store = new_async_store()
async_define(store, "counter", "0")
val value = async_get(store, "counter")
expect(value).to_equal("0")
```

</details>

#### sets value and returns true on change

- sets value and returns true on change
   - Expected: changed is true
   - Expected: async_get(store, "name") equals `bob`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets value and returns true on change")
val store = new_async_store()
async_define(store, "name", "alice")
val changed = async_set(store, "name", "bob")
expect(changed).to_equal(true)
expect(async_get(store, "name")).to_equal("bob")
```

</details>

#### returns false when value unchanged

- returns false when value unchanged
   - Expected: changed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when value unchanged")
val store = new_async_store()
async_define(store, "name", "alice")
val changed = async_set(store, "name", "alice")
expect(changed).to_equal(false)
```

</details>

### async reactive change notifications

#### emits change on primary channel

- emits change on primary channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits change on primary channel")
val store = new_async_store()
async_define(store, "count", "0")
async_set(store, "count", "1")
val notification = store.change_channel.try_recv()
assert_not_equal(notification, nil)
```

</details>

#### emits no notification when value unchanged

- emits no notification when value unchanged
   - Expected: notification equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits no notification when value unchanged")
val store = new_async_store()
async_define(store, "count", "5")
async_set(store, "count", "5")
val notification = store.change_channel.try_recv()
expect(notification).to_equal(nil)
```

</details>

#### observer channel receives changes

- observer channel receives changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("observer channel receives changes")
val store = new_async_store()
async_define(store, "status", "idle")
val observer = async_observe(store)
async_set(store, "status", "busy")
val notification = observer.try_recv()
assert_not_equal(notification, nil)
```

</details>

#### multiple observers each receive change

- multiple observers each receive change


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple observers each receive change")
val store = new_async_store()
async_define(store, "x", "0")
val obs1 = async_observe(store)
val obs2 = async_observe(store)
async_set(store, "x", "1")
val n1 = obs1.try_recv()
val n2 = obs2.try_recv()
assert_not_equal(n1, nil)
assert_not_equal(n2, nil)
```

</details>

#### close stops notifications

- close stops notifications
   - Expected: store.change_channel.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close stops notifications")
val store = new_async_store()
async_define(store, "v", "0")
async_store_close(store)
expect(store.change_channel.is_closed()).to_equal(true)
```

</details>

### async dirty tracking

#### starts clean

- starts clean
   - Expected: async_is_dirty(store) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts clean")
val store = new_async_store()
expect(async_is_dirty(store)).to_equal(false)
```

</details>

#### becomes dirty after set

- becomes dirty after set
   - Expected: async_is_dirty(store) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("becomes dirty after set")
val store = new_async_store()
async_define(store, "v", "0")
async_set(store, "v", "1")
expect(async_is_dirty(store)).to_equal(true)
```

</details>

#### clears dirty flag

- clears dirty flag
   - Expected: async_is_dirty(store) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears dirty flag")
val store = new_async_store()
async_define(store, "v", "0")
async_set(store, "v", "1")
async_clear_dirty(store)
expect(async_is_dirty(store)).to_equal(false)
```

</details>

### AsyncUIState dispatch

#### dispatch sends event to bus

- dispatch sends event to bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch sends event to bus")
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
dispatch(async_state, UIEvent.FocusNext)
val received = bus.events.try_recv()
assert_not_equal(received, nil)
```

</details>

#### dispatch_quit sends Quit event

- dispatch_quit sends Quit event


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch_quit sends Quit event")
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
dispatch_quit(async_state)
val received = bus.events.try_recv()
assert_not_equal(received, nil)
```

</details>

#### dispatch_key sends KeyPress event

- dispatch_key sends KeyPress event


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch_key sends KeyPress event")
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
dispatch_key(async_state, "x")
val received = bus.events.try_recv()
assert_not_equal(received, nil)
```

</details>

#### dispatch_focus_next sends FocusNext event

- dispatch_focus_next sends FocusNext event


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch_focus_next sends FocusNext event")
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
dispatch_focus_next(async_state)
val received = bus.events.try_recv()
assert_not_equal(received, nil)
```

</details>

#### dispatch_focus_prev sends FocusPrev event

- dispatch_focus_prev sends FocusPrev event


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch_focus_prev sends FocusPrev event")
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
dispatch_focus_prev(async_state)
val received = bus.events.try_recv()
assert_not_equal(received, nil)
```

</details>

### AsyncUIState read access

#### get_current returns initial state

- get_current returns initial state
   - Expected: current.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_current returns initial state")
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
val current = get_current(async_state)
expect(current.mode_name()).to_equal("NORMAL")
```

</details>

#### get_current_mode returns mode name

- get_current_mode returns mode name
   - Expected: get_current_mode(async_state) equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_current_mode returns mode name")
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
expect(get_current_mode(async_state)).to_equal("NORMAL")
```

</details>

#### get_focused_id returns focused widget

- get_focused_id returns focused widget
   - Expected: get_focused_id(async_state) equals `ids[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_focused_id returns focused widget")
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
val ids = tree.all_widget_ids()
expect(get_focused_id(async_state)).to_equal(ids[0])
```

</details>

### channel close behaviour

#### closed event channel returns nil on try_recv

- closed event channel returns nil on try_recv
   - Expected: received equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closed event channel returns nil on try_recv")
val bus = new_event_bus()
bus.events.close()
val received = bus.events.try_recv()
expect(received).to_equal(nil)
```

</details>

#### closed event channel is detected by is_closed

- closed event channel is detected by is_closed
   - Expected: bus.events.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closed event channel is detected by is_closed")
val bus = new_event_bus()
bus.events.close()
expect(bus.events.is_closed()).to_equal(true)
```

</details>

#### closed render queue returns nil on try_recv

- closed render queue returns nil on try_recv
   - Expected: received equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closed render queue returns nil on try_recv")
val bus = new_event_bus()
bus.render_queue.close()
val received = bus.render_queue.try_recv()
expect(received).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/async_ui_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UIEventBus creation, event send and try_recv, send_event helper, render queue batching, stop_event_bus, AsyncReactiveStore, async reactive change notifications, async dirty tracking, AsyncUIState dispatch, AsyncUIState read access, channel close behaviour.
- UIEventBus creation
- event send and try_recv
- send_event helper
- render queue batching
- stop_event_bus
- AsyncReactiveStore
- async reactive change notifications
- async dirty tracking
- AsyncUIState dispatch
- AsyncUIState read access
- channel close behaviour

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
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

- Canonical SPipe generation for source `6ddb130f1a507c0e6c3cdb36760c4877fb98139d0d2bf0f5ab1060017b9ed8f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ddb130f1a507c0e6c3cdb36760c4877fb98139d0d2bf0f5ab1060017b9ed8f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ddb130f1a507c0e6c3cdb36760c4877fb98139d0d2bf0f5ab1060017b9ed8f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/async_ui_spec.spl
mirror: doc/06_spec/unit/app/ui/async_ui_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/async_ui_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/async_ui_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/async_ui_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates bus with running flag true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/async_ui_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates bus with open event channel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/async_ui_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates bus with open render queue' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
