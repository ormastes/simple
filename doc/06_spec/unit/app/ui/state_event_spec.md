# State Event Specification

> Tests covering init_state, init_state_with_mode, focus navigation, quit detection, keypress normal mode, escape key handling, mode_name, mode switching via events.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# State Event Specification

## Scenarios

### init_state

#### creates state with Normal mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates state with Normal mode
   - Expected: state.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates state with Normal mode")
val tree = make_test_tree()
val state = init_state(tree)
expect(state.mode_name()).to_equal("NORMAL")
```

</details>

#### sets focused_id to first widget id

- sets focused_id to first widget id
   - Expected: state.focused_id equals `first_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets focused_id to first widget id")
val tree = make_test_tree()
val state = init_state(tree)
# all_widget_ids returns root first
val first_id = tree.all_widget_ids()[0]
expect(state.focused_id).to_equal(first_id)
```

</details>

### init_state_with_mode

#### sets Command mode when given command string

- sets Command mode when given command string
   - Expected: state.mode_name() equals `COMMAND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets Command mode when given command string")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "command")
expect(state.mode_name()).to_equal("COMMAND")
```

</details>

#### sets Insert mode when given insert string

- sets Insert mode when given insert string
   - Expected: state.mode_name() equals `INSERT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets Insert mode when given insert string")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "insert")
expect(state.mode_name()).to_equal("INSERT")
```

</details>

#### sets Menu mode when given menu string

- sets Menu mode when given menu string
   - Expected: state.mode_name() equals `MENU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets Menu mode when given menu string")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "menu")
expect(state.mode_name()).to_equal("MENU")
```

</details>

#### defaults to Normal mode for unknown string

- defaults to Normal mode for unknown string
   - Expected: state.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to Normal mode for unknown string")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "unknown")
expect(state.mode_name()).to_equal("NORMAL")
```

</details>

### focus navigation

#### advances focused_id on FocusNext

- advances focused_id on FocusNext
   - Expected: s2.focused_id equals `ids[1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advances focused_id on FocusNext")
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
val s2 = update_state(state, UIEvent.FocusNext)
# Should move from first id to second id
expect(s2.focused_id).to_equal(ids[1])
```

</details>

#### retreats focused_id on FocusPrev

- retreats focused_id on FocusPrev
   - Expected: s3.focused_id equals `ids[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retreats focused_id on FocusPrev")
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
# Move forward first, then back
val s2 = update_state(state, UIEvent.FocusNext)
val s3 = update_state(s2, UIEvent.FocusPrev)
expect(s3.focused_id).to_equal(ids[0])
```

</details>

#### wraps around at end of list

- wraps around at end of list
   - Expected: s.focused_id equals `ids[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps around at end of list")
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
# Navigate forward through all widgets to wrap
var s = state
var i = 0
while i < ids.len():
    s = update_state(s, UIEvent.FocusNext)
    i = i + 1
# After len() FocusNext events, should wrap to first
expect(s.focused_id).to_equal(ids[0])
```

</details>

#### wraps around at beginning of list

- wraps around at beginning of list
   - Expected: s2.focused_id equals `ids[ids.len() - 1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps around at beginning of list")
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
# FocusPrev from first element should wrap to last
val s2 = update_state(state, UIEvent.FocusPrev)
expect(s2.focused_id).to_equal(ids[ids.len() - 1])
```

</details>

### quit detection

#### is_quit_event returns true for Quit

- is_quit_event returns true for Quit
   - Expected: is_quit_event(UIEvent.Quit) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_quit_event returns true for Quit")
expect(is_quit_event(UIEvent.Quit)).to_equal(true)
```

</details>

#### is_quit_event returns false for FocusNext

- is_quit_event returns false for FocusNext
   - Expected: is_quit_event(UIEvent.FocusNext) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_quit_event returns false for FocusNext")
expect(is_quit_event(UIEvent.FocusNext)).to_equal(false)
```

</details>

#### is_quit_event returns false for KeyPress

- is_quit_event returns false for KeyPress
   - Expected: is_quit_event(UIEvent.KeyPress(key: "q")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_quit_event returns false for KeyPress")
expect(is_quit_event(UIEvent.KeyPress(key: "q"))).to_equal(false)
```

</details>

### keypress normal mode

#### j triggers focus next

- j triggers focus next
   - Expected: s2.focused_id equals `ids[1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("j triggers focus next")
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
val s2 = update_state(state, UIEvent.KeyPress(key: "j"))
expect(s2.focused_id).to_equal(ids[1])
```

</details>

#### k triggers focus prev

- k triggers focus prev
   - Expected: s3.focused_id equals `ids[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("k triggers focus prev")
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
# Move forward first so we can go back
val s2 = update_state(state, UIEvent.KeyPress(key: "j"))
val s3 = update_state(s2, UIEvent.KeyPress(key: "k"))
expect(s3.focused_id).to_equal(ids[0])
```

</details>

#### colon switches to Command mode

- colon switches to Command mode
   - Expected: s2.mode_name() equals `COMMAND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("colon switches to Command mode")
val tree = make_test_tree()
val state = init_state(tree)
val s2 = update_state(state, UIEvent.KeyPress(key: ":"))
expect(s2.mode_name()).to_equal("COMMAND")
```

</details>

#### i switches to Insert mode

- i switches to Insert mode
   - Expected: s2.mode_name() equals `INSERT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i switches to Insert mode")
val tree = make_test_tree()
val state = init_state(tree)
val s2 = update_state(state, UIEvent.KeyPress(key: "i"))
expect(s2.mode_name()).to_equal("INSERT")
```

</details>

### escape key handling

#### escape in Command mode returns to Normal

- escape in Command mode returns to Normal
   - Expected: s2.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escape in Command mode returns to Normal")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "command")
val s2 = update_state(state, UIEvent.KeyPress(key: "escape"))
expect(s2.mode_name()).to_equal("NORMAL")
```

</details>

#### escape in Insert mode returns to Normal

- escape in Insert mode returns to Normal
   - Expected: s2.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escape in Insert mode returns to Normal")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "insert")
val s2 = update_state(state, UIEvent.KeyPress(key: "escape"))
expect(s2.mode_name()).to_equal("NORMAL")
```

</details>

#### escape in Menu mode returns to Normal

- escape in Menu mode returns to Normal
   - Expected: s2.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escape in Menu mode returns to Normal")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "menu")
val s2 = update_state(state, UIEvent.KeyPress(key: "escape"))
expect(s2.mode_name()).to_equal("NORMAL")
```

</details>

### mode_name

#### returns NORMAL for Normal mode

- returns NORMAL for Normal mode
   - Expected: state.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns NORMAL for Normal mode")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "normal")
expect(state.mode_name()).to_equal("NORMAL")
```

</details>

#### returns COMMAND for Command mode

- returns COMMAND for Command mode
   - Expected: state.mode_name() equals `COMMAND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns COMMAND for Command mode")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "command")
expect(state.mode_name()).to_equal("COMMAND")
```

</details>

#### returns INSERT for Insert mode

- returns INSERT for Insert mode
   - Expected: state.mode_name() equals `INSERT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns INSERT for Insert mode")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "insert")
expect(state.mode_name()).to_equal("INSERT")
```

</details>

#### returns MENU for Menu mode

- returns MENU for Menu mode
   - Expected: state.mode_name() equals `MENU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns MENU for Menu mode")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "menu")
expect(state.mode_name()).to_equal("MENU")
```

</details>

### mode switching via events

#### CommandMode event switches to Command

- CommandMode event switches to Command
   - Expected: s2.mode_name() equals `COMMAND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CommandMode event switches to Command")
val tree = make_test_tree()
val state = init_state(tree)
val s2 = update_state(state, UIEvent.CommandMode)
expect(s2.mode_name()).to_equal("COMMAND")
```

</details>

#### InsertMode event switches to Insert

- InsertMode event switches to Insert
   - Expected: s2.mode_name() equals `INSERT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("InsertMode event switches to Insert")
val tree = make_test_tree()
val state = init_state(tree)
val s2 = update_state(state, UIEvent.InsertMode)
expect(s2.mode_name()).to_equal("INSERT")
```

</details>

#### NormalMode event switches to Normal

- NormalMode event switches to Normal
   - Expected: s2.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NormalMode event switches to Normal")
val tree = make_test_tree()
val state = init_state_with_mode(tree, "command")
val s2 = update_state(state, UIEvent.NormalMode)
expect(s2.mode_name()).to_equal("NORMAL")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/state_event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering init_state, init_state_with_mode, focus navigation, quit detection, keypress normal mode, escape key handling, mode_name, mode switching via events.
- init_state
- init_state_with_mode
- focus navigation
- quit detection
- keypress normal mode
- escape key handling
- mode_name
- mode switching via events

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
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

- Canonical SPipe generation for source `e704988d841f6d4403b03012c487c052b185b8736c7585addfc0435f1ec774b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e704988d841f6d4403b03012c487c052b185b8736c7585addfc0435f1ec774b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e704988d841f6d4403b03012c487c052b185b8736c7585addfc0435f1ec774b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/state_event_spec.spl
mirror: doc/06_spec/unit/app/ui/state_event_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/state_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/state_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/state_event_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates state with Normal mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/state_event_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets focused_id to first widget id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/state_event_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets Command mode when given command string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
