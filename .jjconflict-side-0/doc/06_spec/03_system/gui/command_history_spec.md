# Command History Specification

> <details>

<!-- sdn-diagram:id=command_history_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=command_history_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

command_history_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=command_history_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Command History Specification

## Scenarios

### CommandHistory — empty state

#### can_undo is false on empty history

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = CommandHistory.with_defaults()
expect(h.can_undo()).to_equal(false)
```

</details>

#### can_redo is false on empty history

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = CommandHistory.with_defaults()
expect(h.can_redo()).to_equal(false)
```

</details>

### CommandHistory — push and undo

#### push one entry makes can_undo true

1. var h = CommandHistory with defaults
2. h push
   - Expected: h.can_undo() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = CommandHistory.with_defaults()
val e = make_entry(1, "draw", "brush", "before1", "after1")
h.push(e)
expect(h.can_undo()).to_equal(true)
```

</details>

#### push one entry sets entry_count to 1

1. var h = CommandHistory with defaults
2. h push
   - Expected: h.entry_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = CommandHistory.with_defaults()
val e = make_entry(1, "draw", "brush", "before1", "after1")
h.push(e)
expect(h.entry_count()).to_equal(1)
```

</details>

#### undo returns before_snapshot

1. var h = CommandHistory with defaults
2. h push
   - Expected: snap equals `before1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = CommandHistory.with_defaults()
val e = make_entry(1, "draw", "brush", "before1", "after1")
h.push(e)
val snap = h.undo()
expect(snap).to_equal("before1")
```

</details>

#### undo makes can_redo true

1. var h = CommandHistory with defaults
2. h push
3. h undo
   - Expected: h.can_redo() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = CommandHistory.with_defaults()
val e = make_entry(1, "draw", "brush", "before1", "after1")
h.push(e)
h.undo()
expect(h.can_redo()).to_equal(true)
```

</details>

### CommandHistory — redo

#### redo returns after_snapshot

1. var h = CommandHistory with defaults
2. h push
3. h undo
   - Expected: snap equals `after1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = CommandHistory.with_defaults()
val e = make_entry(1, "draw", "brush", "before1", "after1")
h.push(e)
h.undo()
val snap = h.redo()
expect(snap).to_equal("after1")
```

</details>

### CommandHistory — merge

#### two entries with same tool and description merge into one

1. var h = CommandHistory new
2. h push
3. h push
   - Expected: h.entry_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = CommandHistory.new(200, 300)
val e1 = make_entry(1, "stroke", "brush", "s0", "s1")
val e2 = make_entry(2, "stroke", "brush", "s1", "s2")
h.push(e1)
h.push(e2)
expect(h.entry_count()).to_equal(1)
```

</details>

### CommandHistory — max size

#### count stays at max_size when exceeding limit

1. var h = CommandHistory new
2. h push
   - Expected: h.entry_count() <= 3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = CommandHistory.new(3, 0)
var i = 0
while i < 5:
    val e = make_entry(i, "op" + i.to_text(), "tool" + i.to_text(), "b", "a")
    h.push(e)
    i = i + 1
expect(h.entry_count() <= 3).to_equal(true)
```

</details>

### CommandHistory — clear

#### after clear entry_count is 0

1. var h = CommandHistory with defaults
2. h push
3. h clear
   - Expected: h.entry_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = CommandHistory.with_defaults()
val e = make_entry(1, "draw", "brush", "b", "a")
h.push(e)
h.clear()
expect(h.entry_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/command_history_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CommandHistory — empty state
- CommandHistory — push and undo
- CommandHistory — redo
- CommandHistory — merge
- CommandHistory — max size
- CommandHistory — clear

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
