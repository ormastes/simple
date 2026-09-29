# Async Tui Specification

> Tests covering event channel, input parser channel integration, file change detection, state change detection, channel close.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Tui Specification

## Scenarios

### event channel

#### receives events pushed via send

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- receives events pushed via send


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("receives events pushed via send")
val ch = channel_new()
ch.send(UIEvent.FocusNext)
val received = ch.try_recv()
assert_not_equal(received, nil)
```

</details>

#### try_recv returns nil on empty channel

- try_recv returns nil on empty channel
   - Expected: received equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("try_recv returns nil on empty channel")
val ch = channel_new()
val received = ch.try_recv()
expect(received).to_equal(nil)
```

</details>

#### preserves FIFO ordering

- preserves FIFO ordering
   - Expected: fourth equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves FIFO ordering")
val ch = channel_new()
ch.send(UIEvent.FocusNext)
ch.send(UIEvent.FocusPrev)
ch.send(UIEvent.Quit)
val first = ch.try_recv()
val second = ch.try_recv()
val third = ch.try_recv()
# All three should be non-nil
assert_not_equal(first, nil)
assert_not_equal(second, nil)
assert_not_equal(third, nil)
# Fourth should be nil (empty)
val fourth = ch.try_recv()
expect(fourth).to_equal(nil)
```

</details>

#### is_closed returns false before close

- is_closed returns false before close
   - Expected: ch.is_closed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_closed returns false before close")
val ch = channel_new()
expect(ch.is_closed()).to_equal(false)
```

</details>

#### is_closed returns true after close

- is_closed returns true after close
   - Expected: ch.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_closed returns true after close")
val ch = channel_new()
ch.close()
expect(ch.is_closed()).to_equal(true)
```

</details>

#### buffered messages survive close

- buffered messages survive close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("buffered messages survive close")
val ch = channel_new()
ch.send(UIEvent.Quit)
ch.close()
val received = ch.try_recv()
assert_not_equal(received, nil)
```

</details>

### input parser channel integration

#### quit command produces Quit event

- quit command produces Quit event
   - Expected: is_quit_event(event) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quit command produces Quit event")
val event = parse_input_line("quit")
expect(is_quit_event(event)).to_equal(true)
```

</details>

#### j key produces FocusNext when sent through channel

- j key produces FocusNext when sent through channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("j key produces FocusNext when sent through channel")
val ch = channel_new()
val event = parse_input_line("j")
ch.send(event)
val received = ch.try_recv()
assert_not_equal(received, nil)
```

</details>

#### :q command produces Quit event

- :q command produces Quit event
   - Expected: is_quit_event(event) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step(":q command produces Quit event")
val event = parse_input_line(":q")
expect(is_quit_event(event)).to_equal(true)
```

</details>

#### empty line produces KeyPress enter

- empty line produces KeyPress enter


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty line produces KeyPress enter")
val event = parse_input_line("")
# parse_input_line("") returns KeyPress(key: "enter")
val ch = channel_new()
ch.send(event)
val received = ch.try_recv()
assert_not_equal(received, nil)
```

</details>

### file change detection

#### FileChanged event can be sent and received on channel

- FileChanged event can be sent and received on channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FileChanged event can be sent and received on channel")
val ch = channel_new()
ch.send(UIEvent.FileChanged)
val received = ch.try_recv()
assert_not_equal(received, nil)
```

</details>

#### update_tree replaces the tree in state

- update_tree replaces the tree in state
   - Expected: state2.tree.root_id equals `async_root2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("update_tree replaces the tree in state")
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

- update_tree preserves mode and focus
   - Expected: state2.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("update_tree preserves mode and focus")
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

- FocusNext changes focused_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FocusNext changes focused_id")
val tree = make_async_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
val new_state = update_state(state, UIEvent.FocusNext)
assert_not_equal(new_state.focused_id, state.focused_id)
```

</details>

#### CommandMode changes mode name

- CommandMode changes mode name
   - Expected: new_state.mode_name() equals `COMMAND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CommandMode changes mode name")
val tree = make_async_test_tree()
val state = init_state(tree)
val new_state = update_state(state, UIEvent.CommandMode)
expect(new_state.mode_name()).to_equal("COMMAND")
assert_not_equal(new_state.mode_name(), state.mode_name())
```

</details>

#### duplicate normal key does not change state

- duplicate normal key does not change state
   - Expected: new_state.focused_id equals `state.focused_id`
   - Expected: new_state.mode_name() equals `state.mode_name()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("duplicate normal key does not change state")
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

- closed channel rejects new sends gracefully
   - Expected: received equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closed channel rejects new sends gracefully")
val ch = channel_new()
ch.close()
# send on closed channel is a no-op
ch.send(UIEvent.Quit)
# try_recv should return nil (nothing delivered)
val received = ch.try_recv()
expect(received).to_equal(nil)
```

</details>

#### multiple close calls are safe

- multiple close calls are safe
   - Expected: ch.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple close calls are safe")
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
| Source | `test/unit/app/ui/async_tui_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering event channel, input parser channel integration, file change detection, state change detection, channel close.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6c1eaadae3b34759400caaf7e48ebced12141685dd858d45a7ff67e1a06c04c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6c1eaadae3b34759400caaf7e48ebced12141685dd858d45a7ff67e1a06c04c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6c1eaadae3b34759400caaf7e48ebced12141685dd858d45a7ff67e1a06c04c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/async_tui_spec.spl
mirror: doc/06_spec/unit/app/ui/async_tui_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/async_tui_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/async_tui_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/async_tui_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'receives events pushed via send' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/async_tui_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'try_recv returns nil on empty channel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/async_tui_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves FIFO ordering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
