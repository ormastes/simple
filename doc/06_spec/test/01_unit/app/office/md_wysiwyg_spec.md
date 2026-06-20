# md_wysiwyg_spec

> Verifies the Markdown-backed Writer replacement surface: a pure side-by-side view-model pairing each editable Markdown source line with its rendered styled preview, plus per-line edit-and-rerender. The renderer covers headings, paragraphs, fenced code, escaped HTML, and task-list checkboxes through the same document wrapper consumed by IDE TUI and GUI feature checks.

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
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# md_wysiwyg_spec

Verifies the Markdown-backed Writer replacement surface: a pure side-by-side view-model pairing each editable Markdown source line with its rendered styled preview, plus per-line edit-and-rerender. The renderer covers headings, paragraphs, fenced code, escaped HTML, and task-list checkboxes through the same document wrapper consumed by IDE TUI and GUI feature checks.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/ide_office_plugin_suite.md |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/office/md_wysiwyg_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the Markdown-backed Writer replacement surface: a pure side-by-side
view-model pairing each editable Markdown source line with its rendered styled
preview, plus per-line edit-and-rerender. The renderer covers headings,
paragraphs, fenced code, escaped HTML, and task-list checkboxes through the same
document wrapper consumed by IDE TUI and GUI feature checks.

## Syntax

Input is normal Markdown source text split by newline. Source lines stay editable
by `line_no`; preview rows use `.wysiwyg-preview-line` and preserve line numbers
for stable beside-the-line editing.

## Examples

`- [x] Done` renders as a disabled checked checkbox row; `- [ ] Open` renders as
an unchecked disabled checkbox row. Checked edits require the expected source
line to match before replacing a row.

**Requirements:** N/A
**Plan:** doc/03_plan/sys_test/ide_office_plugin_suite.md
**Design:** N/A
**Research:** N/A

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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("hello")
val pane = wysiwyg_preview_pane(view)
expect(pane).to_start_with("<div class=\"wysiwyg-preview\"")
expect(pane).to_contain("data-format=\"markdown-wysiwyg\"")
expect(pane).to_contain("data-format-name=\"Writer Markdown\"")
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

#### renders Markdown task list items as disabled checkboxes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = wysiwyg_preview_document_html("- [x] Done <safe>\n- [ ] Open")
expect(html).to_contain("class=\"markdown-task\"")
expect(html).to_contain("data-task=\"true\" data-checked=\"true\"")
expect(html).to_contain("<input type=\"checkbox\" disabled checked>")
expect(html).to_contain("Done &lt;safe&gt;")
expect(html).to_contain("data-task=\"true\" data-checked=\"false\"")
expect(html).to_contain("<input type=\"checkbox\" disabled>")
expect(html).to_contain("Open</p>")
```

</details>

#### renders strikethrough inline HTML through the document wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = wysiwyg_preview_document_html("Keep ~~old <tag>~~")
expect(html).to_contain("<del>old &lt;tag&gt;</del>")
```

</details>

#### renders inline links through the document wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = wysiwyg_preview_document_html("Read [Docs <x>](docs.md?a=1&b=2)")
expect(html).to_contain("<a href=\"docs.md?a=1&amp;b=2\">Docs &lt;x&gt;</a>")
```

</details>

#### sanitizes unsafe inline links through the document wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = wysiwyg_preview_document_html("Read [Bad](javascript:alert(1))")
expect(html).to_contain("<a href=\"#\">Bad</a>")
```

</details>

#### renders Markdown bullet list lines as HTML lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = wysiwyg_preview_document_html("- First **item**")
expect(html).to_contain("<ul class=\"markdown-list\"")
expect(html).to_contain("<li>First <strong>item</strong></li>")
```

</details>

#### renders Markdown ordered list lines as HTML lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = wysiwyg_preview_document_html("10. First **item**")
expect(html).to_contain("<ol class=\"markdown-list markdown-ordered-list\"")
expect(html).to_contain("<li>First <strong>item</strong></li>")
```

</details>

#### renders Markdown blockquote lines as quote HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = wysiwyg_preview_document_html("> Quote **safe** <x>")
expect(html).to_contain("<blockquote class=\"markdown-quote\"")
expect(html).to_contain(">Quote <strong>safe</strong> &lt;x&gt;</blockquote>")
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

#### keeps edited lines inside fenced code blocks rendered as code

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("```simple\nprint(1)\n```")
val edited = wysiwyg_update_line(view, 1, "print(\"<x>\")")
val preview = wysiwyg_preview_pane(edited)
expect(preview).to_contain("<pre")
expect(preview).to_contain("print(&quot;&lt;x&gt;&quot;)")
expect(preview).to_contain("data-line-no=\"1\"")
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

#### keeps checked edits inside fenced code blocks rendered as code

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = build_wysiwyg_view("```simple\nprint(1)\n```")
val result = wysiwyg_update_line_checked(view, 1, "print(1)", "print(2)")
val preview = wysiwyg_preview_pane(result.view)
expect(result.accepted).to_be(true)
expect(preview).to_contain("<pre")
expect(preview).to_contain(">print(2)</pre>")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/ide_office_plugin_suite.md](doc/03_plan/sys_test/ide_office_plugin_suite.md)


</details>
