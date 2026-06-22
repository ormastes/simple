# Preview Pane Specification

> <details>

<!-- sdn-diagram:id=preview_pane_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=preview_pane_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

preview_pane_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=preview_pane_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Preview Pane Specification

## Scenarios

### preview_pane scroll and bounds

#### render returns empty list for zero height

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(1)
val result = preview_pane_render(pane, 0)
expect(result.len()).to_equal(0)
```

</details>

#### render returns empty list for negative height

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(1)
val result = preview_pane_render(pane, -5)
expect(result.len()).to_equal(0)
```

</details>

#### scroll clamps negative delta to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val scrolled = preview_pane_scroll(pane, -10, 100)
expect(scrolled.viewport_start).to_equal(0)
```

</details>

#### scroll clamps past max_lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val scrolled = preview_pane_scroll(pane, 200, 50)
expect(scrolled.viewport_start).to_equal(49)
```

</details>

#### scroll with max_lines zero returns unchanged pane

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val scrolled = preview_pane_scroll(pane, 5, 0)
expect(scrolled.viewport_start).to_equal(0)
```

</details>

#### scroll with max_lines one clamps to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val scrolled = preview_pane_scroll(pane, 100, 1)
expect(scrolled.viewport_start).to_equal(0)
```

</details>

### preview_pane empty document

#### create produces a pane with viewport_start zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(7)
expect(pane.viewport_start).to_equal(0)
expect(pane.scroll_sync).to_equal(true)
```

</details>

#### update with empty string is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val updated = preview_pane_update(pane, "")
expect(updated.viewport_start).to_equal(0)
```

</details>

#### render on empty document with positive height is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val updated = preview_pane_update(pane, "")
val lines = preview_pane_render(updated, 10)
expect(lines.len()).to_be_less_than(11)
```

</details>

### preview_pane sync scroll edge cases

#### sync scroll with cursor at line 0 sets viewport_start to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val updated = preview_pane_update(pane, "# Hello\nworld\n")
val synced = preview_pane_sync_scroll(updated, 0)
expect(synced.viewport_start).to_equal(0)
```

</details>

#### sync scroll with cursor past last line clamps to last block

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val content = "# Hello\nworld"
val updated = preview_pane_update(pane, content)
val synced = preview_pane_sync_scroll(updated, 9999)
expect(synced.viewport_start).to_be_greater_than(-1)
```

</details>

#### sync scroll disabled returns same viewport_start

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val toggled = preview_pane_toggle_scroll_sync(pane)
val updated = preview_pane_update(toggled, "# Hello\nworld\n")
val synced = preview_pane_sync_scroll(updated, 0)
expect(synced.viewport_start).to_equal(updated.viewport_start)
```

</details>

#### update_for_cursor on empty content does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val result = preview_pane_update_for_cursor(pane, "", 0)
expect(result.viewport_start).to_equal(0)
```

</details>

#### update_for_cursor with cursor past last line is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val result = preview_pane_update_for_cursor(pane, "line1\nline2", 999)
expect(result.viewport_start).to_be_greater_than(-1)
```

</details>

### preview_pane source_line_to_render_line

#### returns non-negative for valid source line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_update(preview_pane_create(0), "# Hello\nworld")
val render_line = preview_pane_source_line_to_render_line(pane, 0)
expect(render_line).to_be_greater_than(-1)
```

</details>

#### returns -1 for out-of-range source line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_update(preview_pane_create(0), "# Hello\nworld")
val render_line = preview_pane_source_line_to_render_line(pane, 9999)
expect(render_line).to_equal(-1)
```

</details>

#### returns -1 for negative source line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_update(preview_pane_create(0), "# Hello\nworld")
val render_line = preview_pane_source_line_to_render_line(pane, -1)
expect(render_line).to_equal(-1)
```

</details>

#### crlf normalisation handles mixed line endings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_create(0)
val updated = preview_pane_update_crlf(pane, "line1\r\nline2\rline3\n")
val lines = preview_pane_render(updated, 10)
expect(lines.len()).to_be_greater_than(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/preview_pane_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- preview_pane scroll and bounds
- preview_pane empty document
- preview_pane sync scroll edge cases
- preview_pane source_line_to_render_line

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
