# Lifecycle Specification

> 1. expect registry handler count

<!-- sdn-diagram:id=lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lifecycle_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lifecycle Specification

## Scenarios

### LifecycleRegistry creation

#### creates an empty registry

1. expect registry handler count
2. expect registry event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
expect registry.handler_count() to_equal 0
expect registry.event_count() to_equal 0
```

</details>

### LifecycleRegistry register handler

#### registers a handler and increments count

1. registry register handler
2. expect registry handler count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
val handler = new_lifecycle_handler("lc_reg_w1")
registry.register_handler(handler)
expect registry.handler_count() to_equal 1
```

</details>

#### retrieves a registered handler by widget id

1. var handler = new lifecycle handler
2. handler = handler with on mount
3. registry register handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
var handler = new_lifecycle_handler("lc_reg_w2")
handler = handler.with_on_mount("mount_cb_1")
registry.register_handler(handler)
val found = registry.get_handler("lc_reg_w2")
expect found != nil to_equal true
```

</details>

#### returns nil for unregistered widget id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
val found = registry.get_handler("lc_reg_nonexistent")
expect found to_be_nil
```

</details>

### LifecycleRegistry unregister handler

#### removes a handler by widget id

1. registry register handler
2. expect registry handler count
3. registry unregister handler
4. expect registry handler count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
val handler = new_lifecycle_handler("lc_unreg_w1")
registry.register_handler(handler)
expect registry.handler_count() to_equal 1
registry.unregister_handler("lc_unreg_w1")
expect registry.handler_count() to_equal 0
```

</details>

#### does nothing for unknown widget id

1. registry register handler
2. registry unregister handler
3. expect registry handler count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
val handler = new_lifecycle_handler("lc_unreg_w2")
registry.register_handler(handler)
registry.unregister_handler("lc_unreg_unknown")
expect registry.handler_count() to_equal 1
```

</details>

### emit_lifecycle_events mount

#### emits Mount event on InsertChild patch

1. patches = patches push
2. emit lifecycle events
3. expect registry event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
val child = WidgetNode.new("lc_mount_child1", "text")
var patches: [UIPatch] = []
patches = patches.push(UIPatch.new(PatchKind.InsertChild, "lc_mount_child1", "lc_mount_parent", child))
emit_lifecycle_events(registry, patches)
expect registry.event_count() to_equal 1
val event = registry.last_event()
val desc = describe_lifecycle_event(event)
expect desc to_contain "mount"
expect desc to_contain "lc_mount_child1"
```

</details>

### emit_lifecycle_events unmount

#### emits Unmount event on RemoveChild patch

1. patches = patches push
2. emit lifecycle events
3. expect registry event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
var patches: [UIPatch] = []
patches = patches.push(UIPatch.new_simple(PatchKind.RemoveChild, "lc_unmount_child1"))
emit_lifecycle_events(registry, patches)
expect registry.event_count() to_equal 1
val event = registry.last_event()
val desc = describe_lifecycle_event(event)
expect desc to_contain "unmount"
expect desc to_contain "lc_unmount_child1"
```

</details>

### emit_lifecycle_events update

#### emits Update event on UpdateProp patch

1. patches = patches push
2. emit lifecycle events
3. expect registry event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
var patches: [UIPatch] = []
patches = patches.push(UIPatch.new_prop(PatchKind.UpdateProp, "lc_update_w1", "content", "new_value"))
emit_lifecycle_events(registry, patches)
expect registry.event_count() to_equal 1
val event = registry.last_event()
val desc = describe_lifecycle_event(event)
expect desc to_contain "update"
expect desc to_contain "lc_update_w1"
expect desc to_contain "content"
```

</details>

### emit_action_event

#### records an action event in the registry

1. emit action event
2. expect registry event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
emit_action_event(registry, "lc_action_btn1", "click")
expect registry.event_count() to_equal 1
val event = registry.last_event()
val desc = describe_lifecycle_event(event)
expect desc to_contain "action"
expect desc to_contain "lc_action_btn1"
expect desc to_contain "click"
```

</details>

### emit_focus_event

#### records a focus event

1. emit focus event
2. expect registry event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
emit_focus_event(registry, "lc_focus_w1")
expect registry.event_count() to_equal 1
val event = registry.last_event()
val desc = describe_lifecycle_event(event)
expect desc to_contain "focus"
expect desc to_contain "lc_focus_w1"
```

</details>

### emit_blur_event

#### records a blur event

1. emit blur event
2. expect registry event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = new_lifecycle_registry()
emit_blur_event(registry, "lc_blur_w1")
expect registry.event_count() to_equal 1
val event = registry.last_event()
val desc = describe_lifecycle_event(event)
expect desc to_contain "blur"
expect desc to_contain "lc_blur_w1"
```

</details>

### with_on_mount modifier

#### sets on_mount prop as handler id

1. var node = text widget
2. node = with on mount
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_widget("lc_mod_mount1", "Hello")
node = with_on_mount(node, "mount_handler_1")
expect node.get_prop("on_mount") to_equal "mount_handler_1"
```

</details>

### with_on_unmount modifier

#### sets on_unmount prop as handler id

1. var node = text widget
2. node = with on unmount
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_widget("lc_mod_unmount1", "Hello")
node = with_on_unmount(node, "unmount_handler_1")
expect node.get_prop("on_unmount") to_equal "unmount_handler_1"
```

</details>

### with_on_update modifier

#### sets on_update prop as handler id

1. var node = text widget
2. node = with on update
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_widget("lc_mod_update1", "Hello")
node = with_on_update(node, "update_handler_1")
expect node.get_prop("on_update") to_equal "update_handler_1"
```

</details>

### with_on_action modifier

#### sets on_action prop as handler id

1. var node = button
2. node = with on action
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = button("lc_mod_action1", "Click", "do_click")
node = with_on_action(node, "action_handler_1")
expect node.get_prop("on_action") to_equal "action_handler_1"
```

</details>

### with_on_focus modifier

#### sets on_focus prop as handler id

1. var node = text widget
2. node = with on focus
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_widget("lc_mod_focus1", "Hello")
node = with_on_focus(node, "focus_handler_1")
expect node.get_prop("on_focus") to_equal "focus_handler_1"
```

</details>

### with_on_blur modifier

#### sets on_blur prop as handler id

1. var node = text widget
2. node = with on blur
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_widget("lc_mod_blur1", "Hello")
node = with_on_blur(node, "blur_handler_1")
expect node.get_prop("on_blur") to_equal "blur_handler_1"
```

</details>

### EffectRunner creation

#### creates an empty runner

1. expect runner pending count
2. expect runner result count
3. expect runner log count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = new_effect_runner()
expect runner.pending_count() to_equal 0
expect runner.result_count() to_equal 0
expect runner.log_count() to_equal 0
```

</details>

### EffectRunner dispatch

#### increments pending count on dispatch

1. runner dispatch effect
2. expect runner pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "test"))
expect runner.pending_count() to_equal 1
```

</details>

#### processes log effect and records message

1. runner dispatch effect
2. runner process effects
3. expect runner pending count
4. expect runner log count
5. expect runner result count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "lifecycle started"))
runner.process_effects()
expect runner.pending_count() to_equal 0
expect runner.log_count() to_equal 1
expect runner.result_count() to_equal 1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LifecycleRegistry creation
- LifecycleRegistry register handler
- LifecycleRegistry unregister handler
- emit_lifecycle_events mount
- emit_lifecycle_events unmount
- emit_lifecycle_events update
- emit_action_event
- emit_focus_event
- emit_blur_event
- with_on_mount modifier
- with_on_unmount modifier
- with_on_update modifier
- with_on_action modifier
- with_on_focus modifier
- with_on_blur modifier
- EffectRunner creation
- EffectRunner dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
