# Lifecycle Specification

> Tests covering LifecycleRegistry creation, LifecycleRegistry register handler, LifecycleRegistry unregister handler, emit_lifecycle_events mount, emit_lifecycle_events unmount, emit_lifecycle_events update, emit_action_event, emit_focus_event, emit_blur_event, with_on_mount modifier, with_on_unmount modifier, with_on_update modifier, with_on_action modifier, with_on_focus modifier, with_on_blur modifier, EffectRunner creation, EffectRunner dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lifecycle Specification

## Scenarios

### LifecycleRegistry creation

#### creates an empty registry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates an empty registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an empty registry")
val registry = new_lifecycle_registry()
expect registry.handler_count() to_equal 0
expect registry.event_count() to_equal 0
```

</details>

### LifecycleRegistry register handler

#### registers a handler and increments count

- registers a handler and increments count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a handler and increments count")
val registry = new_lifecycle_registry()
val handler = new_lifecycle_handler("lc_reg_w1")
registry.register_handler(handler)
expect registry.handler_count() to_equal 1
```

</details>

#### retrieves a registered handler by widget id

- retrieves a registered handler by widget id


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves a registered handler by widget id")
val registry = new_lifecycle_registry()
var handler = new_lifecycle_handler("lc_reg_w2")
handler = handler.with_on_mount("mount_cb_1")
registry.register_handler(handler)
val found = registry.get_handler("lc_reg_w2")
expect found != nil to_equal true
```

</details>

#### returns nil for unregistered widget id

- returns nil for unregistered widget id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for unregistered widget id")
val registry = new_lifecycle_registry()
val found = registry.get_handler("lc_reg_nonexistent")
expect found to_be_nil
```

</details>

### LifecycleRegistry unregister handler

#### removes a handler by widget id

- removes a handler by widget id


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a handler by widget id")
val registry = new_lifecycle_registry()
val handler = new_lifecycle_handler("lc_unreg_w1")
registry.register_handler(handler)
expect registry.handler_count() to_equal 1
registry.unregister_handler("lc_unreg_w1")
expect registry.handler_count() to_equal 0
```

</details>

#### does nothing for unknown widget id

- does nothing for unknown widget id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does nothing for unknown widget id")
val registry = new_lifecycle_registry()
val handler = new_lifecycle_handler("lc_unreg_w2")
registry.register_handler(handler)
registry.unregister_handler("lc_unreg_unknown")
expect registry.handler_count() to_equal 1
```

</details>

### emit_lifecycle_events mount

#### emits Mount event on InsertChild patch

- emits Mount event on InsertChild patch


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits Mount event on InsertChild patch")
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

- emits Unmount event on RemoveChild patch


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits Unmount event on RemoveChild patch")
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

- emits Update event on UpdateProp patch


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits Update event on UpdateProp patch")
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

- records an action event in the registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records an action event in the registry")
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

- records a focus event


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a focus event")
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

- records a blur event


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a blur event")
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

- sets on_mount prop as handler id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets on_mount prop as handler id")
var node = text_widget("lc_mod_mount1", "Hello")
node = with_on_mount(node, "mount_handler_1")
expect node.get_prop("on_mount") to_equal "mount_handler_1"
```

</details>

### with_on_unmount modifier

#### sets on_unmount prop as handler id

- sets on_unmount prop as handler id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets on_unmount prop as handler id")
var node = text_widget("lc_mod_unmount1", "Hello")
node = with_on_unmount(node, "unmount_handler_1")
expect node.get_prop("on_unmount") to_equal "unmount_handler_1"
```

</details>

### with_on_update modifier

#### sets on_update prop as handler id

- sets on_update prop as handler id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets on_update prop as handler id")
var node = text_widget("lc_mod_update1", "Hello")
node = with_on_update(node, "update_handler_1")
expect node.get_prop("on_update") to_equal "update_handler_1"
```

</details>

### with_on_action modifier

#### sets on_action prop as handler id

- sets on_action prop as handler id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets on_action prop as handler id")
var node = button("lc_mod_action1", "Click", "do_click")
node = with_on_action(node, "action_handler_1")
expect node.get_prop("on_action") to_equal "action_handler_1"
```

</details>

### with_on_focus modifier

#### sets on_focus prop as handler id

- sets on_focus prop as handler id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets on_focus prop as handler id")
var node = text_widget("lc_mod_focus1", "Hello")
node = with_on_focus(node, "focus_handler_1")
expect node.get_prop("on_focus") to_equal "focus_handler_1"
```

</details>

### with_on_blur modifier

#### sets on_blur prop as handler id

- sets on_blur prop as handler id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets on_blur prop as handler id")
var node = text_widget("lc_mod_blur1", "Hello")
node = with_on_blur(node, "blur_handler_1")
expect node.get_prop("on_blur") to_equal "blur_handler_1"
```

</details>

### EffectRunner creation

#### creates an empty runner

- creates an empty runner


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an empty runner")
val runner = new_effect_runner()
expect runner.pending_count() to_equal 0
expect runner.result_count() to_equal 0
expect runner.log_count() to_equal 0
```

</details>

### EffectRunner dispatch

#### increments pending count on dispatch

- increments pending count on dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments pending count on dispatch")
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "test"))
expect runner.pending_count() to_equal 1
```

</details>

#### processes log effect and records message

- processes log effect and records message


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes log effect and records message")
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
| Source | `test/unit/app/ui/lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LifecycleRegistry creation, LifecycleRegistry register handler, LifecycleRegistry unregister handler, emit_lifecycle_events mount, emit_lifecycle_events unmount, emit_lifecycle_events update, emit_action_event, emit_focus_event, emit_blur_event, with_on_mount modifier, with_on_unmount modifier, with_on_update modifier, with_on_action modifier, with_on_focus modifier, with_on_blur modifier, EffectRunner creation, EffectRunner dispatch.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd0d95e9266ad4c444d7d69edefa2a6e3cdca56c5b5f21690fa1493dd436893c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd0d95e9266ad4c444d7d69edefa2a6e3cdca56c5b5f21690fa1493dd436893c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd0d95e9266ad4c444d7d69edefa2a6e3cdca56c5b5f21690fa1493dd436893c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/lifecycle_spec.spl
mirror: doc/06_spec/unit/app/ui/lifecycle_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/lifecycle_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an empty registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/lifecycle_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers a handler and increments count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/lifecycle_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retrieves a registered handler by widget id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
