# Editor Session Specification

> <details>

<!-- sdn-diagram:id=editor_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_session_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Session Specification

## Scenarios

### editor document — metadata

#### defines EditorDocumentId with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/types.spl")
expect(src.contains("class EditorDocumentId:")).to_equal(true)
expect(src.contains("value: i64")).to_equal(true)
```

</details>

#### defines EditorDocument with buffer and language_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("class EditorDocument:")).to_equal(true)
expect(src.contains("buffer: EditorBuffer")).to_equal(true)
expect(src.contains("language_id: text")).to_equal(true)
expect(src.contains("content: text")).to_equal(true)
expect(src.contains("modified: bool")).to_equal(true)
```

</details>

#### has from_path and empty constructors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("static fn from_path(path: text) -> EditorDocument")).to_equal(true)
expect(src.contains("static fn empty() -> EditorDocument")).to_equal(true)
```

</details>

#### detects language from file extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("fn _language_id_from_path(path: text) -> text")).to_equal(true)
expect(src.contains(".spl")).to_equal(true)
expect(src.contains("\"simple\"")).to_equal(true)
expect(src.contains("\"markdown\"")).to_equal(true)
```

</details>

#### provides display_name from path basename

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("fn display_name() -> text")).to_equal(true)
expect(src.contains("[No Name]")).to_equal(true)
```

</details>

### editor tab — tab and group

#### defines EditorTab with pane and path metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/tab.spl")
expect(src.contains("struct EditorTab:")).to_equal(true)
expect(src.contains("pane_id: i64")).to_equal(true)
expect(src.contains("path: text")).to_equal(true)
expect(src.contains("title: text")).to_equal(true)
expect(src.contains("modified: bool")).to_equal(true)
```

</details>

#### defines TabBar with tabs list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/tab.spl")
expect(src.contains("struct TabBar:")).to_equal(true)
expect(src.contains("tabs: [EditorTab]")).to_equal(true)
expect(src.contains("active_index: i64")).to_equal(true)
```

</details>

#### has tab bar add and activate helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/tab.spl")
expect(src.contains("fn tab_bar_add(bar: TabBar, tab: EditorTab) -> TabBar")).to_equal(true)
expect(src.contains("fn tab_bar_activate(bar: TabBar, idx: i64) -> TabBar")).to_equal(true)
```

</details>

#### has close_tab by pane id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/tab.spl")
expect(src.contains("fn tab_bar_close(bar: TabBar, pane_id: i64) -> TabBar")).to_equal(true)
expect(src.contains("if t.pane_id != pane_id")).to_equal(true)
```

</details>

### editor layout — split panes

#### defines EditorLayout struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("struct EditorLayout:")).to_equal(true)
expect(src.contains("groups: [EditorGroup]")).to_equal(true)
expect(src.contains("active_group_index: i64")).to_equal(true)
expect(src.contains("orientation: LayoutOrientation")).to_equal(true)
```

</details>

#### creates default layout with one group

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("fn layout_new() -> EditorLayout")).to_equal(true)
expect(src.contains("groups: [EditorGroup(id: 1, tabs: [], active_tab_index: 0)]")).to_equal(true)
```

</details>

#### supports group replacement and rect computation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("fn editor_layout_with_group(layout: EditorLayout, index: i64, group: EditorGroup) -> EditorLayout")).to_equal(true)
expect(src.contains("fn editor_layout_compute_rects(layout: EditorLayout, x: i64, y: i64, w: i64, h: i64) -> [SplitRect]")).to_equal(true)
```

</details>

#### supports active group lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("fn editor_layout_active_group_index(layout: EditorLayout) -> i64")).to_equal(true)
expect(src.contains("layout.active_group_id")).to_equal(true)
```

</details>

#### provides group count and active group access

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("fn editor_layout_group_count_raw(layout: EditorLayout) -> i64")).to_equal(true)
expect(src.contains("fn editor_layout_group_at(layout: EditorLayout, index: i64) -> EditorGroup")).to_equal(true)
```

</details>

### edit session — central state

#### defines EditSession class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("class EditSession:")).to_equal(true)
expect(src.contains("documents: [EditorDocument]")).to_equal(true)
expect(src.contains("layout: EditorLayout")).to_equal(true)
expect(src.contains("mode: EditorMode")).to_equal(true)
```

</details>

#### has static new constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("static fn new() -> EditSession")).to_equal(true)
```

</details>

#### has open_file that avoids duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me open_file(path: text) -> EditorDocumentId")).to_equal(true)
expect(src.contains("existing_doc.path() == path")).to_equal(true)
```

</details>

#### has open_empty for new documents

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me open_empty() -> EditorDocumentId")).to_equal(true)
```

</details>

#### has close_tab and save_active

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me close_tab()")).to_equal(true)
expect(src.contains("fn save_active() -> bool")).to_equal(true)
```

</details>

#### has switch_tab with delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me switch_tab(delta: i64)")).to_equal(true)
```

</details>

#### has split_editor creating new group

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me split_editor()")).to_equal(true)
expect(src.contains("split_tree_split")).to_equal(true)
```

</details>

#### has focus_next_group and focus_prev_group

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me focus_next_group()")).to_equal(true)
expect(src.contains("me focus_prev_group()")).to_equal(true)
```

</details>

#### provides active_document and active_buffer accessors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("fn active_document() -> EditorDocument")).to_equal(true)
expect(src.contains("fn active_buffer() -> EditorBuffer")).to_equal(true)
expect(src.contains("fn active_doc_id() -> EditorDocumentId")).to_equal(true)
```

</details>

#### tracks pane id generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("next_pane_id: i64")).to_equal(true)
expect(src.contains("val new_id = me.next_pane_id")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor document — metadata
- editor tab — tab and group
- editor layout — split panes
- edit session — central state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
