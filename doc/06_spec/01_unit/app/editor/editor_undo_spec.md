# Editor Undo Specification

> Verifies that the TextEditor undo stack correctly captures line snapshots before each mutating operation and restores them on undo, bounded at 50 entries (oldest dropped when full).

<!-- sdn-diagram:id=editor_undo_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_undo_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_undo_spec -> std
editor_undo_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_undo_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Undo Specification

Verifies that the TextEditor undo stack correctly captures line snapshots before each mutating operation and restores them on undo, bounded at 50 entries (oldest dropped when full).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B2 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/app/editor/editor_undo_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the TextEditor undo stack correctly captures line snapshots
before each mutating operation and restores them on undo, bounded at 50
entries (oldest dropped when full).

## Scenarios

### TextEditor undo

#### insert then undo restores original state

1. var ed = TextEditor new
2. ed insert char
3. ed insert char
4. ed undo
5. ed undo
   - Expected: ed.lines[0] equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
# initial state: one empty line
val before = ed.lines[0]
ed.insert_char("a")
ed.insert_char("b")
ed.undo()
ed.undo()
expect(ed.lines[0]).to_equal(before)
```

</details>

#### undo on empty stack shows message

1. var ed = TextEditor new
2. ed undo
   - Expected: ed.status_message equals `Already at oldest change`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.undo()
expect(ed.status_message).to_equal("Already at oldest change")
```

</details>

#### undo stack bounded at 50 entries

1. var ed = TextEditor new
2. ed insert char


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
var i = 0
while i < 60:
    ed.insert_char("x")
    i = i + 1
# Stack must not exceed 50
expect(ed.undo_stack.len()).to_be_less_than(51)
```

</details>

#### undo after delete_char restores line

1. var ed = TextEditor new
2. ed insert char
3. ed insert char
4. ed delete char
5. ed undo
   - Expected: ed.lines[0] equals `before_delete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.insert_char("h")
ed.insert_char("i")
# move cursor back and delete
ed.cursor_col = 1
val before_delete = ed.lines[0]
ed.delete_char()
ed.undo()
expect(ed.lines[0]).to_equal(before_delete)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
