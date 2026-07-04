# Async Tui Specification

> 1. ch send

<!-- sdn-diagram:id=async_tui_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_tui_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_tui_spec -> std
async_tui_spec -> common
async_tui_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_tui_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Tui Specification

## Scenarios

### event channel

#### receives events pushed via send

1. ch send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.send(UIEvent.FocusNext)
val received = ch.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### try_recv returns nil on empty channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val received = ch.try_recv()
expect(received == nil).to_equal(true)
```

</details>

#### preserves FIFO ordering

1. ch send
2. ch send
3. ch send
   - Expected: first != nil is true
   - Expected: second != nil is true
   - Expected: third != nil is true
   - Expected: fourth == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.send(UIEvent.FocusNext)
ch.send(UIEvent.FocusPrev)
ch.send(UIEvent.Quit)
val first = ch.try_recv()
val second = ch.try_recv()
val third = ch.try_recv()
# All three should be non-nil
expect(first != nil).to_equal(true)
expect(second != nil).to_equal(true)
expect(third != nil).to_equal(true)
# Fourth should be nil (empty)
val fourth = ch.try_recv()
expect(fourth == nil).to_equal(true)
```

</details>

#### is_closed returns false before close

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
expect(ch.is_closed()).to_equal(false)
```

</details>

#### is_closed returns true after close

1. ch close
   - Expected: ch.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.close()
expect(ch.is_closed()).to_equal(true)
```

</details>

#### buffered messages survive close

1. ch send
2. ch close
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.send(UIEvent.Quit)
ch.close()
val received = ch.try_recv()
expect(received != nil).to_equal(true)
```

</details>

### input parser channel integration

#### quit command produces Quit event

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_input_line("quit")
expect(is_quit_event(event)).to_equal(true)
```

</details>

#### j key produces FocusNext when sent through channel

1. ch send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val event = parse_input_line("j")
ch.send(event)
val received = ch.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### :q command produces Quit event

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_input_line(":q")
expect(is_quit_event(event)).to_equal(true)
```

</details>

#### empty line produces KeyPress enter

1. ch send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_input_line("")
# parse_input_line("") returns KeyPress(key: "enter")
val ch = channel_new()
ch.send(event)
val received = ch.try_recv()
expect(received != nil).to_equal(true)
```

</details>

### file change detection

#### FileChanged event can be sent and received on channel

1. ch send
   - Expected: received != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.send(UIEvent.FileChanged)
val received = ch.try_recv()
expect(received != nil).to_equal(true)
```

</details>

#### update_tree replaces the tree in state

1. text widget
   - Expected: state2.tree.root_id equals `async_root2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree1 = make_async_test_tree()
val state1 = init_state(tree1)
# Build a different tree
val root2 = column("async_root2", [
    text_widget("async_w4", "Fourth")
])
val tree2 = build_tree(root2)
val state2 = update_tree(state1, tree2)
expect(state2.tree.root_id).to_equal("async_root2")
```

</details>

#### update_tree preserves mode and focus

1. text widget
   - Expected: state2.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree1 = make_async_test_tree()
val state1 = init_state(tree1)
val focused = update_state(state1, UIEvent.FocusNext)
val root2 = column("async_alt", [
    text_widget("async_a1", "Alt")
])
val tree2 = build_tree(root2)
val state2 = update_tree(focused, tree2)
# Mode should be preserved
expect(state2.mode_name()).to_equal("NORMAL")
```

</details>

### state change detection

#### FocusNext changes focused_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_async_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
val new_state = update_state(state, UIEvent.FocusNext)
expect(new_state.focused_id != state.focused_id).to_equal(true)
```

</details>

#### CommandMode changes mode name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_async_test_tree()
val state = init_state(tree)
val new_state = update_state(state, UIEvent.CommandMode)
expect(new_state.mode_name()).to_equal("COMMAND")
expect(new_state.mode_name() != state.mode_name()).to_equal(true)
```

</details>

#### duplicate normal key does not change state

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_async_test_tree()
val state = init_state(tree)
# An unknown key in Normal mode should not change state
val new_state = update_state(state, UIEvent.KeyPress(key: "z"))
expect(new_state.focused_id).to_equal(state.focused_id)
expect(new_state.mode_name()).to_equal(state.mode_name())
```

</details>

### channel close

#### closed channel rejects new sends gracefully

1. ch close
2. ch send
   - Expected: received == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.close()
# send on closed channel is a no-op
ch.send(UIEvent.Quit)
# try_recv should return nil (nothing delivered)
val received = ch.try_recv()
expect(received == nil).to_equal(true)
```

</details>

#### multiple close calls are safe

1. ch close
2. ch close
   - Expected: ch.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.close()
ch.close()
expect(ch.is_closed()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/async_tui_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- event channel
- input parser channel integration
- file change detection
- state change detection
- channel close

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
