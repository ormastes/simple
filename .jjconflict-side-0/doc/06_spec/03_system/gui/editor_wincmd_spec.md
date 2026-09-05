# Editor Wincmd Specification

> <details>

<!-- sdn-diagram:id=editor_wincmd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_wincmd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_wincmd_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_wincmd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Wincmd Specification

## Scenarios

### wincmd dispatch — struct and function

#### defines WincmdResult struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("struct WincmdResult:")).to_equal(true)
expect(src.contains("handled: bool")).to_equal(true)
expect(src.contains("message: text")).to_equal(true)
expect(src.contains("quit: bool")).to_equal(true)
```

</details>

#### defines wincmd_dispatch function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("fn wincmd_dispatch(session: EditSession, key: text, rects: [SplitRect]) -> WincmdResult")).to_equal(true)
```

</details>

#### handles focus direction keys h/j/k/l

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("focus_direction(\"left\"")).to_equal(true)
expect(src.contains("focus_direction(\"down\"")).to_equal(true)
expect(src.contains("focus_direction(\"up\"")).to_equal(true)
expect(src.contains("focus_direction(\"right\"")).to_equal(true)
```

</details>

#### handles swap keys H/J/K/L

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("split_find_neighbor")).to_equal(true)
expect(src.contains("session.layout.tree.swap")).to_equal(true)
```

</details>

#### handles split keys v and s

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("session.split_editor()")).to_equal(true)
expect(src.contains("session.split_editor_horizontal()")).to_equal(true)
```

</details>

#### handles close and only keys c/q/o

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("session.close_active_group()")).to_equal(true)
expect(src.contains("session.close_other_groups()")).to_equal(true)
```

</details>

#### handles resize keys +/- and equalize =

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("session.layout.tree.resize")).to_equal(true)
expect(src.contains("session.layout.tree.equalize()")).to_equal(true)
```

</details>

### commands — split and resize entries

#### has split-horizontal and split-vertical dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"split-horizontal\"")).to_equal(true)
expect(src.contains("\"split-vertical\"")).to_equal(true)
```

</details>

#### has close-other-groups command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"close-other-groups\"")).to_equal(true)
```

</details>

#### has resize-grow and resize-shrink commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"resize-grow\"")).to_equal(true)
expect(src.contains("\"resize-shrink\"")).to_equal(true)
```

</details>

#### parses :sp and :vs commandline aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"sp\"")).to_equal(true)
expect(src.contains("\"vs\"")).to_equal(true)
expect(src.contains("\"only\"")).to_equal(true)
```

</details>

### keybindings — wincmd prefix

#### has ctrl_w binding for wincmd-prefix in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("ctrl_w")).to_equal(true)
expect(src.contains("wincmd-prefix")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_wincmd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wincmd dispatch — struct and function
- commands — split and resize entries
- keybindings — wincmd prefix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
