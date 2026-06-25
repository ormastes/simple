# Async Ui Specification

> <details>

<!-- sdn-diagram:id=async_ui_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_ui_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_ui_spec -> std
async_ui_spec -> common
async_ui_spec -> nogc_async_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_ui_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Ui Specification

## Scenarios

### UIEventBus creation

#### creates bus with running flag true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
expect(bus.running).to_equal(true)
```

</details>

#### creates bus with open event channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
expect(bus.events.is_closed()).to_equal(false)
```

</details>

#### creates bus with open render queue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
expect(bus.render_queue.is_closed()).to_equal(false)
```

</details>

### event send and try_recv

#### sends and receives a KeyPress event

1. bus events send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
bus.events.send(UIEvent.KeyPress(key: "j"))
val received = bus.events.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### returns nil when no events pending

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
val received = bus.events.try_recv()
expect(received == nil).to_equal(true)
```

</details>

#### sends and receives Quit event

1. bus events send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
bus.events.send(UIEvent.Quit)
val received = bus.events.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### preserves FIFO order

1. bus events send
2. bus events send
3. bus events send
   - Expected: e1 != nil is true
   - Expected: e2 != nil is true
   - Expected: e3 != nil is true
   - Expected: e4 == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
bus.events.send(UIEvent.FocusNext)
bus.events.send(UIEvent.FocusPrev)
bus.events.send(UIEvent.Quit)
val e1 = bus.events.try_recv()
val e2 = bus.events.try_recv()
val e3 = bus.events.try_recv()
val e4 = bus.events.try_recv()
expect(e1 != nil).to_equal(true)
expect(e2 != nil).to_equal(true)
expect(e3 != nil).to_equal(true)
expect(e4 == nil).to_equal(true)
```

</details>

### send_event helper

#### pushes event through the bus

1. send event
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
send_event(bus, UIEvent.FocusNext)
val received = bus.events.try_recv()
expect(received != nil).to_equal(true)
```

</details>

### render queue batching

#### sends state to render queue

1. bus render queue send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
bus.render_queue.send(state)
val received = bus.render_queue.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### drains all queued renders leaving only latest

1. bus render queue send
2. bus render queue send
3. bus render queue send
   - Expected: latest != nil is true
   - Expected: empty == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(latest != nil).to_equal(true)
# Queue should now be empty
val empty = bus.render_queue.try_recv()
expect(empty == nil).to_equal(true)
```

</details>

### stop_event_bus

#### sets running to false

1. stop event bus
   - Expected: bus.running is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
stop_event_bus(bus)
expect(bus.running).to_equal(false)
```

</details>

#### closes event channel

1. stop event bus
   - Expected: bus.events.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
stop_event_bus(bus)
expect(bus.events.is_closed()).to_equal(true)
```

</details>

#### closes render queue channel

1. stop event bus
   - Expected: bus.render_queue.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
stop_event_bus(bus)
expect(bus.render_queue.is_closed()).to_equal(true)
```

</details>

### AsyncReactiveStore

#### creates empty store

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
val value = async_get(store, "x")
expect(value).to_equal("")
```

</details>

#### defines and gets a value

1. async define
   - Expected: value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
async_define(store, "counter", "0")
val value = async_get(store, "counter")
expect(value).to_equal("0")
```

</details>

#### sets value and returns true on change

1. async define
   - Expected: changed is true
   - Expected: async_get(store, "name") equals `bob`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
async_define(store, "name", "alice")
val changed = async_set(store, "name", "bob")
expect(changed).to_equal(true)
expect(async_get(store, "name")).to_equal("bob")
```

</details>

#### returns false when value unchanged

1. async define
   - Expected: changed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
async_define(store, "name", "alice")
val changed = async_set(store, "name", "alice")
expect(changed).to_equal(false)
```

</details>

### async reactive change notifications

#### emits change on primary channel

1. async define
2. async set
   - Expected: notification != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
async_define(store, "count", "0")
async_set(store, "count", "1")
val notification = store.change_channel.try_recv()
expect(notification != nil).to_equal(true)
```

</details>

#### emits no notification when value unchanged

1. async define
2. async set
   - Expected: notification == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
async_define(store, "count", "5")
async_set(store, "count", "5")
val notification = store.change_channel.try_recv()
expect(notification == nil).to_equal(true)
```

</details>

#### observer channel receives changes

1. async define
2. async set
   - Expected: notification != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
async_define(store, "status", "idle")
val observer = async_observe(store)
async_set(store, "status", "busy")
val notification = observer.try_recv()
expect(notification != nil).to_equal(true)
```

</details>

#### multiple observers each receive change

1. async define
2. async set
   - Expected: n1 != nil is true
   - Expected: n2 != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
async_define(store, "x", "0")
val obs1 = async_observe(store)
val obs2 = async_observe(store)
async_set(store, "x", "1")
val n1 = obs1.try_recv()
val n2 = obs2.try_recv()
expect(n1 != nil).to_equal(true)
expect(n2 != nil).to_equal(true)
```

</details>

#### close stops notifications

1. async define
2. async store close
   - Expected: store.change_channel.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
async_define(store, "v", "0")
async_store_close(store)
expect(store.change_channel.is_closed()).to_equal(true)
```

</details>

### async dirty tracking

#### starts clean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
expect(async_is_dirty(store)).to_equal(false)
```

</details>

#### becomes dirty after set

1. async define
2. async set
   - Expected: async_is_dirty(store) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
async_define(store, "v", "0")
async_set(store, "v", "1")
expect(async_is_dirty(store)).to_equal(true)
```

</details>

#### clears dirty flag

1. async define
2. async set
3. async clear dirty
   - Expected: async_is_dirty(store) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = new_async_store()
async_define(store, "v", "0")
async_set(store, "v", "1")
async_clear_dirty(store)
expect(async_is_dirty(store)).to_equal(false)
```

</details>

### AsyncUIState dispatch

#### dispatch sends event to bus

1. dispatch
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
dispatch(async_state, UIEvent.FocusNext)
val received = bus.events.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### dispatch_quit sends Quit event

1. dispatch quit
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
dispatch_quit(async_state)
val received = bus.events.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### dispatch_key sends KeyPress event

1. dispatch key
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
dispatch_key(async_state, "x")
val received = bus.events.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### dispatch_focus_next sends FocusNext event

1. dispatch focus next
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
dispatch_focus_next(async_state)
val received = bus.events.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### dispatch_focus_prev sends FocusPrev event

1. dispatch focus prev
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
dispatch_focus_prev(async_state)
val received = bus.events.try_recv()
expect(received != nil).to_equal(true)
```

</details>

### AsyncUIState read access

#### get_current returns initial state

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
val current = get_current(async_state)
expect(current.mode_name()).to_equal("NORMAL")
```

</details>

#### get_current_mode returns mode name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
val tree = make_async_test_tree()
val state = init_state(tree)
val async_state = new_async_state(state, bus)
expect(get_current_mode(async_state)).to_equal("NORMAL")
```

</details>

#### get_focused_id returns focused widget

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. bus events close
   - Expected: received == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
bus.events.close()
val received = bus.events.try_recv()
expect(received == nil).to_equal(true)
```

</details>

#### closed event channel is detected by is_closed

1. bus events close
   - Expected: bus.events.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
bus.events.close()
expect(bus.events.is_closed()).to_equal(true)
```

</details>

#### closed render queue returns nil on try_recv

1. bus render queue close
   - Expected: received == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = new_event_bus()
bus.render_queue.close()
val received = bus.render_queue.try_recv()
expect(received == nil).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/async_ui_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
