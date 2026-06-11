# Event API Spec

> Unit tests for the Simple browser engine Event API.

<!-- sdn-diagram:id=event_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=event_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

event_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=event_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Event API Spec

Unit tests for the Simple browser engine Event API.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/event_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the Simple browser engine Event API.

## Scenarios

### Event API - Listener Registration

#### adds an event listener

1. node add event listener
   - Expected: el.event_listener_types.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = BeDomNode.element("button")
node_add_event_listener(el, "click", "handle_click", false)
expect(el.event_listener_types.len()).to_equal(1)
```

</details>

#### removes an event listener

1. node add event listener
2. node remove event listener
   - Expected: el.event_listener_types.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = BeDomNode.element("button")
node_add_event_listener(el, "click", "handle_click", false)
node_remove_event_listener(el, "click", "handle_click")
expect(el.event_listener_types.len()).to_equal(0)
```

</details>

#### adds capture phase listener

1. node add event listener
   - Expected: el.event_listener_capture[0] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = BeDomNode.element("div")
node_add_event_listener(el, "click", "cap_handler", true)
expect(el.event_listener_capture[0]).to_equal(true)
```

</details>

### Event API - Event Creation

#### creates an event with type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = event_create("click", "btn1")
expect(ev.event_type).to_equal("click")
```

</details>

#### creates event with target id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = event_create("click", "btn1")
expect(ev.target_id).to_equal("btn1")
```

</details>

#### created events bubble by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = event_create("keydown", "input1")
expect(ev.bubbles).to_equal(true)
```

</details>

### Event API - Event Control

#### prevents default action

1. event prevent default
   - Expected: ev.default_prevented is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = event_create("submit", "form1")
event_prevent_default(ev)
expect(ev.default_prevented).to_equal(true)
```

</details>

#### stops propagation

1. event stop propagation
   - Expected: ev.propagation_stopped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = event_create("click", "btn1")
event_stop_propagation(ev)
expect(ev.propagation_stopped).to_equal(true)
```

</details>

### Event API - Dispatch

#### dispatches returns actions for registered listeners

1. node add event listener
   - Expected: actions.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = BeDomNode.element("button")
node_add_event_listener(el, "click", "on_click", false)
val ev = event_create("click", "btn")
val actions = event_dispatch(el, ev)
expect(actions.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
