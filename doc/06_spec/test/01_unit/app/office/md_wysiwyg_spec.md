# Md Wysiwyg Specification

> _A view pairs source lines with rendered previews from one document._

<!-- sdn-diagram:id=md_wysiwyg_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_wysiwyg_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_wysiwyg_spec -> std
md_wysiwyg_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_wysiwyg_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Wysiwyg Specification

## Scenarios

### markdown WYSIWYG view: source and preview panes
_A view pairs source lines with rendered previews from one document._

#### has one row per source line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("alpha\nbeta\ngamma")
expect(wysiwyg_line_count(view)).to_equal(3)
```

</details>

#### preserves the source in the source pane

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("alpha\nbeta")
val pane = wysiwyg_source_pane(view)
expect(pane).to_equal("alpha\nbeta")
```

</details>

#### renders styled HTML in the preview pane

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("hello")
val pane = wysiwyg_preview_pane(view)
expect(pane).to_start_with("<div class=\"wysiwyg-preview\"")
expect(pane).to_contain("data-format=\"markdown-wysiwyg\"")
expect(pane).to_contain("data-line-count=\"1\"")
expect(pane).to_contain("class=\"wysiwyg-preview-line\" data-line-no=\"0\"")
expect(pane).to_contain("line-height: 1.5;")
expect(pane).to_contain(">hello</p>")
```

</details>

#### exposes a CSS-backed document wrapper for GUI WYSIWYG rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = wysiwyg_preview_document_html("# Title\n<script>alert(1)</script>")
expect(wysiwyg_preview_css()).to_contain(".wysiwyg-preview")
expect(html).to_start_with("<style>.wysiwyg-preview")
expect(html).to_contain("box-sizing: border-box")
expect(html).to_contain(".wysiwyg-preview-line")
expect(html).to_contain("&lt;script&gt;alert(1)&lt;/script&gt;")
expect(html).to_contain("data-line-count=\"2\"")
expect(html).to_contain("data-line-no=\"1\"")
expect(html).to_contain("style=\"font-family:")
```

</details>

### markdown WYSIWYG view: beside-the-line editing
_Editing one line updates only that row's source and preview._

#### edits a single line's source

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("first\nsecond")
val edited = wysiwyg_update_line(view, 1, "changed")
val pane = wysiwyg_source_pane(edited)
expect(pane).to_equal("first\nchanged")
```

</details>

#### re-renders only the edited line's preview

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("first\nsecond")
val edited = wysiwyg_update_line(view, 1, "changed")
val preview = wysiwyg_preview_pane(edited)
expect(preview).to_contain(">first</p>")
expect(preview).to_contain(">changed</p>")
```

</details>

#### accepts checked edits only when expected source matches actual source

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("first\nsecond")
val result = wysiwyg_update_line_checked(view, 1, "second", "changed")
expect(result.accepted).to_be(true)
expect(result.reason).to_equal("updated")
expect(result.diff).to_equal("@@ line 1 @@\n- second\n+ changed")
expect(wysiwyg_source_pane(result.view)).to_equal("first\nchanged")
```

</details>

#### rejects stale checked edits with expected and actual source

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("first\nactual")
val result = wysiwyg_update_line_checked(view, 1, "expected", "changed")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("stale-line")
expect(result.actual_source).to_equal("actual")
expect(result.diff).to_equal("@@ line 1 @@\nexpected: expected\nactual: actual\nrejected: changed")
expect(wysiwyg_source_pane(result.view)).to_equal("first\nactual")
```

</details>

#### rejects checked edits for missing lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("first")
val result = wysiwyg_update_line_checked(view, 3, "expected", "changed")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("line-not-found")
expect(result.actual_source).to_equal("<missing>")
expect(wysiwyg_source_pane(result.view)).to_equal("first")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `/tmp/simple-office-next47/test/01_unit/app/office/md_wysiwyg_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown WYSIWYG view: source and preview panes
- markdown WYSIWYG view: beside-the-line editing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
