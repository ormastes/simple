# Wiki Panel Specification

> <details>

<!-- sdn-diagram:id=wiki_panel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wiki_panel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wiki_panel_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wiki_panel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wiki Panel Specification

## Scenarios

### wiki_panel empty vault

#### new panel has zero rows and selected zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = wiki_panel_new("Tags")
expect(panel.rows.len()).to_equal(0)
expect(panel.selected).to_equal(0)
```

</details>

#### target_path returns empty on empty panel

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = wiki_panel_new("Tags")
val path = wiki_panel_target_path(panel)
expect(path).to_equal("")
```

</details>

#### target_line returns 0 on empty panel

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = wiki_panel_new("Tags")
val line = wiki_panel_target_line(panel)
expect(line).to_equal(0)
```

</details>

#### select on empty panel clamps to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = wiki_panel_new("Tags")
val selected = wiki_panel_select(panel, 5)
expect(selected.selected).to_equal(0)
```

</details>

#### select negative on empty panel clamps to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = wiki_panel_new("Tags")
val selected = wiki_panel_select(panel, -3)
expect(selected.selected).to_equal(0)
```

</details>

#### render on empty panel returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = wiki_panel_new("Tags")
val lines = wiki_panel_render(panel, 10)
expect(lines.len()).to_equal(0)
```

</details>

#### render_row out of range returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = wiki_panel_new("Tags")
val row = wiki_panel_render_row(panel, 0)
expect(row).to_equal("")
```

</details>

#### from_backlinks with empty list produces empty panel

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty_links: [MdWikiLink] = []
val panel = wiki_panel_from_backlinks(empty_links)
expect(panel.rows.len()).to_equal(0)
expect(panel.title).to_equal("Backlinks")
```

</details>

#### from_tags with empty list produces empty panel

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty_tags: [MdWikiTag] = []
val panel = wiki_panel_from_tags(empty_tags)
expect(panel.rows.len()).to_equal(0)
```

</details>

### wiki_panel selection clamping

#### select clamped to last row when index exceeds bounds

- rows push
- rows push
   - Expected: selected.selected equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rows: [WikiPanelRow] = []
rows.push(WikiPanelRow(icon: "#", label: "alpha", detail: "a.md:1", path: "a.md", line: 0))
rows.push(WikiPanelRow(icon: "#", label: "beta", detail: "b.md:2", path: "b.md", line: 1))
val panel = wiki_panel_with_rows("Tags", rows)
val selected = wiki_panel_select(panel, 99)
expect(selected.selected).to_equal(1)
```

</details>

#### select negative clamped to 0

- rows push
   - Expected: selected.selected equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rows: [WikiPanelRow] = []
rows.push(WikiPanelRow(icon: "#", label: "alpha", detail: "a.md:1", path: "a.md", line: 0))
val panel = wiki_panel_with_rows("Tags", rows)
val selected = wiki_panel_select(panel, -5)
expect(selected.selected).to_equal(0)
```

</details>

#### target_path returns correct path after clamped select

- rows push
- rows push
   - Expected: wiki_panel_target_path(selected) equals `b.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rows: [WikiPanelRow] = []
rows.push(WikiPanelRow(icon: "#", label: "alpha", detail: "a.md:1", path: "a.md", line: 0))
rows.push(WikiPanelRow(icon: "#", label: "beta", detail: "b.md:2", path: "b.md", line: 1))
val panel = wiki_panel_with_rows("Tags", rows)
val selected = wiki_panel_select(panel, 1)
expect(wiki_panel_target_path(selected)).to_equal("b.md")
```

</details>

### wiki_panel duplicate tags and long names

#### duplicate tag labels are both shown in render

- rows push
- rows push
   - Expected: lines.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rows: [WikiPanelRow] = []
rows.push(WikiPanelRow(icon: "#", label: "rust", detail: "a.md:1", path: "a.md", line: 0))
rows.push(WikiPanelRow(icon: "#", label: "rust", detail: "b.md:2", path: "b.md", line: 1))
val panel = wiki_panel_with_rows("Tags", rows)
val lines = wiki_panel_render(panel, 10)
expect(lines.len()).to_equal(2)
```

</details>

#### very long tag name is rendered without crash

- rows push
   - Expected: lines.len() equals `1`
   - Expected: lines[0] contains `long_tag`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val long_tag = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
var rows: [WikiPanelRow] = []
rows.push(WikiPanelRow(icon: "#", label: long_tag, detail: "x.md:1", path: "x.md", line: 0))
val panel = wiki_panel_with_rows("Tags", rows)
val lines = wiki_panel_render(panel, 5)
expect(lines.len()).to_equal(1)
expect(lines[0].contains(long_tag)).to_equal(true)
```

</details>

#### render height zero returns empty list

- rows push
   - Expected: lines.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rows: [WikiPanelRow] = []
rows.push(WikiPanelRow(icon: "#", label: "tag", detail: "x.md:1", path: "x.md", line: 0))
val panel = wiki_panel_with_rows("Tags", rows)
val lines = wiki_panel_render(panel, 0)
expect(lines.len()).to_equal(0)
```

</details>

### wiki_panel render_row

#### selected row has > prefix

- rows push
- rows push
   - Expected: row0.starts_with("  ") is true
   - Expected: row1.starts_with("> ") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rows: [WikiPanelRow] = []
rows.push(WikiPanelRow(icon: "#", label: "tag1", detail: "a.md:1", path: "a.md", line: 0))
rows.push(WikiPanelRow(icon: "#", label: "tag2", detail: "b.md:2", path: "b.md", line: 1))
val panel = wiki_panel_with_rows("Tags", rows)
val selected = wiki_panel_select(panel, 1)
val row0 = wiki_panel_render_row(selected, 0)
val row1 = wiki_panel_render_row(selected, 1)
expect(row0.starts_with("  ")).to_equal(true)
expect(row1.starts_with("> ")).to_equal(true)
```

</details>

#### render_row with negative index returns empty string

- rows push
   - Expected: wiki_panel_render_row(panel, -1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rows: [WikiPanelRow] = []
rows.push(WikiPanelRow(icon: "#", label: "tag", detail: "x.md:1", path: "x.md", line: 0))
val panel = wiki_panel_with_rows("Tags", rows)
expect(wiki_panel_render_row(panel, -1)).to_equal("")
```

</details>

#### render_row with index equal to rows.len returns empty string

- rows push
   - Expected: wiki_panel_render_row(panel, 1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rows: [WikiPanelRow] = []
rows.push(WikiPanelRow(icon: "#", label: "tag", detail: "x.md:1", path: "x.md", line: 0))
val panel = wiki_panel_with_rows("Tags", rows)
expect(wiki_panel_render_row(panel, 1)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/wiki_panel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wiki_panel empty vault
- wiki_panel selection clamping
- wiki_panel duplicate tags and long names
- wiki_panel render_row

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
