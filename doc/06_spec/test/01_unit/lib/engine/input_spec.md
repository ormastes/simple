# input_spec

> Engine Input — InputManager pure state logic tests (NO FFI calls)

<!-- sdn-diagram:id=input_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=input_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

input_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=input_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# input_spec

Engine Input — InputManager pure state logic tests (NO FFI calls)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/input_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Input — InputManager pure state logic tests (NO FFI calls)

Tests InputManager creation, action binding/unbinding, and initial state
queries. Does not call poll() to avoid FFI dependencies.

## Scenarios

### InputManager

#### create with dummy handle 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = InputManager.create(0)
expect(mgr.event_loop_handle).to_equal(0)
expect(mgr.should_close).to_equal(false)
expect(mgr.action_names.len()).to_equal(0)
```

</details>

#### bind_action adds a binding

1. var mgr = InputManager create
2. mgr bind action
   - Expected: mgr.action_names.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = InputManager.create(0)
val binding = ActionBinding.key_only("jump", KeyCode(code: 32))
mgr.bind_action("jump", binding)
expect(mgr.action_names.len()).to_equal(1)
```

</details>

#### bind_action replaces existing binding

1. var mgr = InputManager create
2. mgr bind action
3. mgr bind action
   - Expected: mgr.action_names.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = InputManager.create(0)
val binding1 = ActionBinding.key_only("jump", KeyCode(code: 32))
val binding2 = ActionBinding.key_only("jump", KeyCode(code: 87))
mgr.bind_action("jump", binding1)
mgr.bind_action("jump", binding2)
# Should still have only 1 binding, not 2
expect(mgr.action_names.len()).to_equal(1)
```

</details>

#### unbind_action removes a binding

1. var mgr = InputManager create
2. mgr bind action
   - Expected: mgr.action_names.len() equals `1`
3. mgr unbind action
   - Expected: mgr.action_names.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = InputManager.create(0)
val binding = ActionBinding.key_only("jump", KeyCode(code: 32))
mgr.bind_action("jump", binding)
expect(mgr.action_names.len()).to_equal(1)
mgr.unbind_action("jump")
expect(mgr.action_names.len()).to_equal(0)
```

</details>

#### is_key_pressed returns false initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = InputManager.create(0)
val result = mgr.is_key_pressed(KeyCode(code: 32))
expect(result).to_equal(false)
```

</details>

#### is_action_pressed returns false initially

1. var mgr = InputManager create
2. mgr bind action
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = InputManager.create(0)
val binding = ActionBinding.key_only("jump", KeyCode(code: 32))
mgr.bind_action("jump", binding)
val result = mgr.is_action_pressed("jump")
expect(result).to_equal(false)
```

</details>

#### is_action_pressed returns false for unbound action

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = InputManager.create(0)
val result = mgr.is_action_pressed("nonexistent")
expect(result).to_equal(false)
```

</details>

#### window_should_close returns false initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = InputManager.create(0)
expect(mgr.window_should_close()).to_equal(false)
```

</details>

#### get_mouse returns default state

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = InputManager.create(0)
val mouse = mgr.get_mouse()
val mx_i = mouse.x * 1000.0
val my_i = mouse.y * 1000.0
expect(mx_i).to_be_greater_than(-1.0)
expect(mx_i).to_be_less_than(1.0)
expect(my_i).to_be_greater_than(-1.0)
expect(my_i).to_be_less_than(1.0)
```

</details>

#### get_action_strength returns 0.0 for unbound action

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = InputManager.create(0)
val strength = mgr.get_action_strength("nonexistent")
val s_i = strength * 1000.0
expect(s_i).to_be_greater_than(-1.0)
expect(s_i).to_be_less_than(1.0)
```

</details>

#### bind_key_action convenience method works

1. var mgr = InputManager create
2. mgr bind key action
   - Expected: mgr.action_names.len() equals `1`
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = InputManager.create(0)
mgr.bind_key_action("shoot", KeyCode(code: 70))
expect(mgr.action_names.len()).to_equal(1)
val result = mgr.is_action_pressed("shoot")
expect(result).to_equal(false)
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
