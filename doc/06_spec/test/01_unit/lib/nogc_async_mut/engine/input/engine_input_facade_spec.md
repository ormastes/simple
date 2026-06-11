# Engine Input Facade Specification

> 1. var mgr = InputManager create

<!-- sdn-diagram:id=engine_input_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_input_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_input_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_input_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Input Facade Specification

## Scenarios

### nogc_async_mut engine input facade

#### re-exports pure input state and binding behavior

1. var mgr = InputManager create
   - Expected: mgr.window_should_close() is false
2. mgr bind action
   - Expected: mgr.action_names.len() equals `1`
   - Expected: mgr.is_action_pressed("jump") is false
   - Expected: mgr.is_mouse_pressed(MouseButtonId(code: 0)) is false
3. mgr bind key action
   - Expected: mgr.action_names.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ButtonState.JustPressed.is_pressed()).to_equal(true)
expect(ButtonState.JustReleased.is_just_released()).to_equal(true)
val mouse = MouseState.initial()
expect(mouse.left).to_equal(ButtonState.Released)

var mgr = InputManager.create(0)
expect(mgr.window_should_close()).to_equal(false)
val binding = ActionBinding.key_only("jump", KeyCode(code: 32))
mgr.bind_action("jump", binding)
expect(mgr.action_names.len()).to_equal(1)
expect(mgr.is_action_pressed("jump")).to_equal(false)
expect(mgr.is_mouse_pressed(MouseButtonId(code: 0))).to_equal(false)
mgr.bind_key_action("shoot", KeyCode(code: 70))
expect(mgr.action_names.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/engine/input/engine_input_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut engine input facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
