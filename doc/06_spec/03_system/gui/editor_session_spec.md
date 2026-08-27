# Editor Session Specification

> Tests covering editor document — metadata, editor tab — tab and group, editor layout — split panes, edit session — central state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Session Specification

## Scenarios

### editor document — metadata

#### defines EditorDocumentId with value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines EditorDocumentId with value
   - Expected: src contains `class EditorDocumentId:`
   - Expected: src contains `value: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines EditorDocumentId with value")
val src = read_text("src/lib/editor/00.common/types.spl")
expect(src.contains("class EditorDocumentId:")).to_equal(true)
expect(src.contains("value: i64")).to_equal(true)
```

</details>

#### defines EditorDocument with buffer and language_id

- defines EditorDocument with buffer and language_id
   - Expected: src contains `class EditorDocument:`
   - Expected: src contains `buffer: EditorBuffer`
   - Expected: src contains `language_id: text`
   - Expected: src contains `content: text`
   - Expected: src contains `modified: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines EditorDocument with buffer and language_id")
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("class EditorDocument:")).to_equal(true)
expect(src.contains("buffer: EditorBuffer")).to_equal(true)
expect(src.contains("language_id: text")).to_equal(true)
expect(src.contains("content: text")).to_equal(true)
expect(src.contains("modified: bool")).to_equal(true)
```

</details>

#### has from_path and empty constructors

- has from_path and empty constructors
   - Expected: src contains `static fn from_path(path: text) -> EditorDocument`
   - Expected: src contains `static fn empty() -> EditorDocument`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has from_path and empty constructors")
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("static fn from_path(path: text) -> EditorDocument")).to_equal(true)
expect(src.contains("static fn empty() -> EditorDocument")).to_equal(true)
```

</details>

#### detects language from file extension

- detects language from file extension
   - Expected: src contains `fn _language_id_from_path(path: text) -> text`
   - Expected: src contains `.spl`
   - Expected: src contains `"simple"`
   - Expected: src contains `"markdown"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects language from file extension")
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("fn _language_id_from_path(path: text) -> text")).to_equal(true)
expect(src.contains(".spl")).to_equal(true)
expect(src.contains("\"simple\"")).to_equal(true)
expect(src.contains("\"markdown\"")).to_equal(true)
```

</details>

#### provides display_name from path basename

- provides display_name from path basename
   - Expected: src contains `fn display_name() -> text`
   - Expected: src contains `[No Name]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides display_name from path basename")
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("fn display_name() -> text")).to_equal(true)
expect(src.contains("[No Name]")).to_equal(true)
```

</details>

### editor tab — tab and group

#### defines EditorTab with pane and path metadata

- defines EditorTab with pane and path metadata
   - Expected: src contains `struct EditorTab:`
   - Expected: src contains `pane_id: i64`
   - Expected: src contains `path: text`
   - Expected: src contains `title: text`
   - Expected: src contains `modified: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines EditorTab with pane and path metadata")
val src = read_text("src/lib/editor/view/tab.spl")
expect(src.contains("struct EditorTab:")).to_equal(true)
expect(src.contains("pane_id: i64")).to_equal(true)
expect(src.contains("path: text")).to_equal(true)
expect(src.contains("title: text")).to_equal(true)
expect(src.contains("modified: bool")).to_equal(true)
```

</details>

#### defines TabBar with tabs list

- defines TabBar with tabs list
   - Expected: src contains `struct TabBar:`
   - Expected: src contains `tabs: [EditorTab]`
   - Expected: src contains `active_index: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines TabBar with tabs list")
val src = read_text("src/lib/editor/view/tab.spl")
expect(src.contains("struct TabBar:")).to_equal(true)
expect(src.contains("tabs: [EditorTab]")).to_equal(true)
expect(src.contains("active_index: i64")).to_equal(true)
```

</details>

#### has tab bar add and activate helpers

- has tab bar add and activate helpers
   - Expected: src contains `fn tab_bar_add(bar: TabBar, tab: EditorTab) -> TabBar`
   - Expected: src contains `fn tab_bar_activate(bar: TabBar, idx: i64) -> TabBar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has tab bar add and activate helpers")
val src = read_text("src/lib/editor/view/tab.spl")
expect(src.contains("fn tab_bar_add(bar: TabBar, tab: EditorTab) -> TabBar")).to_equal(true)
expect(src.contains("fn tab_bar_activate(bar: TabBar, idx: i64) -> TabBar")).to_equal(true)
```

</details>

#### has close_tab by pane id

- has close_tab by pane id
   - Expected: src contains `fn tab_bar_close(bar: TabBar, pane_id: i64) -> TabBar`
   - Expected: src contains `if t.pane_id != pane_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has close_tab by pane id")
val src = read_text("src/lib/editor/view/tab.spl")
expect(src.contains("fn tab_bar_close(bar: TabBar, pane_id: i64) -> TabBar")).to_equal(true)
expect(src.contains("if t.pane_id != pane_id")).to_equal(true)
```

</details>

### editor layout — split panes

#### defines EditorLayout struct

- defines EditorLayout struct
   - Expected: src contains `struct EditorLayout:`
   - Expected: src contains `groups: [EditorGroup]`
   - Expected: src contains `active_group_index: i64`
   - Expected: src contains `orientation: LayoutOrientation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines EditorLayout struct")
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("struct EditorLayout:")).to_equal(true)
expect(src.contains("groups: [EditorGroup]")).to_equal(true)
expect(src.contains("active_group_index: i64")).to_equal(true)
expect(src.contains("orientation: LayoutOrientation")).to_equal(true)
```

</details>

#### creates default layout with one group

- creates default layout with one group
   - Expected: src contains `fn layout_new() -> EditorLayout`
   - Expected: src contains `groups: [EditorGroup(id: 1, tabs: [], active_tab_index: 0)]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates default layout with one group")
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("fn layout_new() -> EditorLayout")).to_equal(true)
expect(src.contains("groups: [EditorGroup(id: 1, tabs: [], active_tab_index: 0)]")).to_equal(true)
```

</details>

#### supports group replacement and rect computation

- supports group replacement and rect computation
   - Expected: src contains `fn editor_layout_with_group(layout: EditorLayout, index: i64, group: EditorGr... (full value in folded executable source)`
   - Expected: src contains `fn editor_layout_compute_rects(layout: EditorLayout, x: i64, y: i64, w: i64, ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports group replacement and rect computation")
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("fn editor_layout_with_group(layout: EditorLayout, index: i64, group: EditorGroup) -> EditorLayout")).to_equal(true)
expect(src.contains("fn editor_layout_compute_rects(layout: EditorLayout, x: i64, y: i64, w: i64, h: i64) -> [SplitRect]")).to_equal(true)
```

</details>

#### supports active group lookup

- supports active group lookup
   - Expected: src contains `fn editor_layout_active_group_index(layout: EditorLayout) -> i64`
   - Expected: src contains `layout.active_group_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports active group lookup")
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("fn editor_layout_active_group_index(layout: EditorLayout) -> i64")).to_equal(true)
expect(src.contains("layout.active_group_id")).to_equal(true)
```

</details>

#### provides group count and active group access

- provides group count and active group access
   - Expected: src contains `fn editor_layout_group_count_raw(layout: EditorLayout) -> i64`
   - Expected: src contains `fn editor_layout_group_at(layout: EditorLayout, index: i64) -> EditorGroup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides group count and active group access")
val src = read_text("src/lib/editor/view/layout.spl")
expect(src.contains("fn editor_layout_group_count_raw(layout: EditorLayout) -> i64")).to_equal(true)
expect(src.contains("fn editor_layout_group_at(layout: EditorLayout, index: i64) -> EditorGroup")).to_equal(true)
```

</details>

### edit session — central state

#### defines EditSession class

- defines EditSession class
   - Expected: src contains `class EditSession:`
   - Expected: src contains `documents: [EditorDocument]`
   - Expected: src contains `layout: EditorLayout`
   - Expected: src contains `mode: EditorMode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines EditSession class")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("class EditSession:")).to_equal(true)
expect(src.contains("documents: [EditorDocument]")).to_equal(true)
expect(src.contains("layout: EditorLayout")).to_equal(true)
expect(src.contains("mode: EditorMode")).to_equal(true)
```

</details>

#### has static new constructor

- has static new constructor
   - Expected: src contains `static fn new() -> EditSession`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has static new constructor")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("static fn new() -> EditSession")).to_equal(true)
```

</details>

#### has open_file that avoids duplicates

- has open_file that avoids duplicates
   - Expected: src contains `me open_file(path: text) -> EditorDocumentId`
   - Expected: src contains `existing_doc.path() == path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has open_file that avoids duplicates")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me open_file(path: text) -> EditorDocumentId")).to_equal(true)
expect(src.contains("existing_doc.path() == path")).to_equal(true)
```

</details>

#### has open_empty for new documents

- has open_empty for new documents
   - Expected: src contains `me open_empty() -> EditorDocumentId`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has open_empty for new documents")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me open_empty() -> EditorDocumentId")).to_equal(true)
```

</details>

#### has close_tab and save_active

- has close_tab and save_active
   - Expected: src contains `me close_tab()`
   - Expected: src contains `fn save_active() -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has close_tab and save_active")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me close_tab()")).to_equal(true)
expect(src.contains("fn save_active() -> bool")).to_equal(true)
```

</details>

#### has switch_tab with delta

- has switch_tab with delta
   - Expected: src contains `me switch_tab(delta: i64)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has switch_tab with delta")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me switch_tab(delta: i64)")).to_equal(true)
```

</details>

#### has split_editor creating new group

- has split_editor creating new group
   - Expected: src contains `me split_editor()`
   - Expected: src contains `split_tree_split`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has split_editor creating new group")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me split_editor()")).to_equal(true)
expect(src.contains("split_tree_split")).to_equal(true)
```

</details>

#### has focus_next_group and focus_prev_group

- has focus_next_group and focus_prev_group
   - Expected: src contains `me focus_next_group()`
   - Expected: src contains `me focus_prev_group()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has focus_next_group and focus_prev_group")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me focus_next_group()")).to_equal(true)
expect(src.contains("me focus_prev_group()")).to_equal(true)
```

</details>

#### provides active_document and active_buffer accessors

- provides active_document and active_buffer accessors
   - Expected: src contains `fn active_document() -> EditorDocument`
   - Expected: src contains `fn active_buffer() -> EditorBuffer`
   - Expected: src contains `fn active_doc_id() -> EditorDocumentId`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides active_document and active_buffer accessors")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("fn active_document() -> EditorDocument")).to_equal(true)
expect(src.contains("fn active_buffer() -> EditorBuffer")).to_equal(true)
expect(src.contains("fn active_doc_id() -> EditorDocumentId")).to_equal(true)
```

</details>

#### tracks pane id generation

- tracks pane id generation
   - Expected: src contains `next_pane_id: i64`
   - Expected: src contains `val new_id = me.next_pane_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks pane id generation")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering editor document — metadata, editor tab — tab and group, editor layout — split panes, edit session — central state.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f74962643ca325b394b22b36cf035c38200cf1fd5773f4794c76cf58cbfa9c9b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f74962643ca325b394b22b36cf035c38200cf1fd5773f4794c76cf58cbfa9c9b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f74962643ca325b394b22b36cf035c38200cf1fd5773f4794c76cf58cbfa9c9b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_session_spec.spl
mirror: doc/06_spec/03_system/gui/editor_session_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_session_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines EditorDocumentId with value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_session_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines EditorDocument with buffer and language_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_session_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has from_path and empty constructors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
