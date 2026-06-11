# Browser Renderer Hit Test Events Specification

> <details>

<!-- sdn-diagram:id=browser_renderer_hit_test_events_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_renderer_hit_test_events_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_renderer_hit_test_events_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_renderer_hit_test_events_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Hit Test Events Specification

## Scenarios

### Browser renderer hit-test event routing

#### keeps id hit testing for the deepest layout box

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = _interactive_layout()

expect(hit_test(layout, 25, 25)).to_equal("save")
expect(hit_test(layout, 15, 15)).to_equal("panel")
expect(hit_test(layout, 200, 200)).to_equal("")
```

</details>

#### returns a root to target path for pointer coordinates

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = _interactive_layout()

val path = hit_test_path(layout, 25, 25)

expect(path.len()).to_equal(3)
expect(path[0].id).to_equal("root")
expect(path[1].id).to_equal("panel")
expect(path[2].id).to_equal("save")
```

</details>

#### dispatches click through capture target and bubble phases from hit test

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = _interactive_layout()

val dispatch = hit_test_dispatch_click(layout, 25, 25)

expect(dispatch.event.target_id).to_equal("save")
expect(dispatch.default_action).to_equal("button-activate")
expect(dispatch.default_action_allowed).to_equal(true)
expect(dispatch.actions.len()).to_equal(6)
expect(dispatch.actions[0]).to_equal("root-capture")
expect(dispatch.phases[0]).to_equal("capture")
expect(dispatch.actions[1]).to_equal("panel-capture")
expect(dispatch.phases[1]).to_equal("capture")
expect(dispatch.actions[2]).to_equal("inline-click")
expect(dispatch.phases[2]).to_equal("target")
expect(dispatch.actions[3]).to_equal("target-listener")
expect(dispatch.phases[3]).to_equal("target")
expect(dispatch.actions[4]).to_equal("panel-bubble")
expect(dispatch.phases[4]).to_equal("bubble")
expect(dispatch.actions[5]).to_equal("root-bubble")
expect(dispatch.phases[5]).to_equal("bubble")
```

</details>

#### dispatches raw pointer-derived events through hit-tested paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = _interactive_layout()

val dispatch = hit_test_dispatch_pointer_event(layout, 25, 25, "mousedown")

expect(dispatch.event.event_type).to_equal("mousedown")
expect(dispatch.event.target_id).to_equal("save")
expect(dispatch.event.client_x).to_equal(25)
expect(dispatch.event.client_y).to_equal(25)
expect(dispatch.event.button).to_equal(0)
expect(dispatch.event.buttons).to_equal(1)
expect(dispatch.event.pointer_id).to_equal(1)
expect(dispatch.event.pointer_type).to_equal("mouse")
expect(dispatch.actions.len()).to_equal(2)
expect(dispatch.actions[0]).to_equal("root-down-capture")
expect(dispatch.phases[0]).to_equal("capture")
expect(dispatch.actions[1]).to_equal("target-down")
expect(dispatch.phases[1]).to_equal("target")
expect(dispatch.default_action_allowed).to_equal(false)
```

</details>

#### dispatches pointer-derived events with modifier key state

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = _interactive_layout()

val dispatch = hit_test_dispatch_pointer_event_with_modifiers(layout, 25, 25, "mousedown", true, false, true, true)

expect(dispatch.event.target_id).to_equal("save")
expect(dispatch.event.client_x).to_equal(25)
expect(dispatch.event.alt_key).to_equal(true)
expect(dispatch.event.ctrl_key).to_equal(false)
expect(dispatch.event.meta_key).to_equal(true)
expect(dispatch.event.shift_key).to_equal(true)
```

</details>

#### synthesizes click after pointer down and up on the same target

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = _interactive_layout()

val activation = hit_test_dispatch_pointer_activation(layout, 25, 25, 30, 30)

expect(activation.down.event.event_type).to_equal("mousedown")
expect(activation.down.event.target_id).to_equal("save")
expect(activation.up.event.event_type).to_equal("mouseup")
expect(activation.up.event.target_id).to_equal("save")
expect(activation.click_synthesized).to_equal(true)
expect(activation.click.event.event_type).to_equal("click")
expect(activation.click.event.client_x).to_equal(30)
expect(activation.click.event.client_y).to_equal(30)
expect(activation.click.event.detail).to_equal(1)
expect(activation.click.event.buttons).to_equal(0)
expect(activation.click.default_action).to_equal("button-activate")
expect(activation.click.actions[2]).to_equal("inline-click")
```

</details>

#### does not synthesize click when pointer up lands on a different target

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = _interactive_layout()

val activation = hit_test_dispatch_pointer_activation(layout, 25, 25, 15, 15)

expect(activation.down.event.target_id).to_equal("save")
expect(activation.up.event.target_id).to_equal("panel")
expect(activation.click_synthesized).to_equal(false)
expect(activation.click.event.target_id).to_equal("")
expect(activation.click.actions.len()).to_equal(0)
```

</details>

#### returns an empty dispatch for pointer misses

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = _interactive_layout()

val dispatch = hit_test_dispatch_click(layout, 200, 200)

expect(dispatch.event.target_id).to_equal("")
expect(dispatch.actions.len()).to_equal(0)
expect(dispatch.default_action_allowed).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser renderer hit-test event routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
