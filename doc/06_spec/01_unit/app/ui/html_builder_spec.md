# Html Builder Specification

> <details>

<!-- sdn-diagram:id=html_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_builder_spec -> std
html_builder_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Builder Specification

## Scenarios

### html builder helpers

#### escapes html special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(html_escape("<a b=\"c&d\">'x'</a>")).to_equal("&lt;a b=&quot;c&amp;d&quot;&gt;&#39;x&#39;&lt;/a&gt;")
```

</details>

#### builds a complete html page with escaped title

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = html_page("A&B", "body { color:red; }", "<main>Hi</main>")
expect(page).to_contain("<!DOCTYPE html>")
expect(page).to_contain("<title>A&amp;B</title>")
expect(page).to_contain("body { color:red; }")
expect(page).to_contain("<main>Hi</main>")
```

</details>

#### builds grid containers without reordering items

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = html_grid(2, "8px", ["<span>A</span>", "<span>B</span>"])
expect(html).to_equal("<div style=\"display:grid; grid-template-columns:repeat(2, 1fr); gap:8px\">\n  <span>A</span>\n  <span>B</span>\n</div>\n")
```

</details>

#### builds cards with escaped titles and raw body content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = html_card("A < B", "<p>Body</p>")
expect(html).to_contain("<h3>A &lt; B</h3>")
expect(html).to_contain("<div class=\"card-body\"><p>Body</p></div>")
```

</details>

#### builds progress bars with clamped values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = html_progress_bar(140)
expect(html).to_contain("width:100%")
expect(html).to_contain("var(--green, #3fb950)")
```

</details>

#### builds tables with escaped headers and cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = html_table(["Name"], [["A&B"], ["<tag>"]])
expect(html).to_contain("<th>Name</th>")
expect(html).to_contain("<td>A&amp;B</td>")
expect(html).to_contain("<td>&lt;tag&gt;</td>")
```

</details>

#### builds reset and dark theme css snippets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(css_reset()).to_contain("box-sizing: border-box")
expect(css_dark_theme()).to_contain("--bg: #0d1117")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/html_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- html builder helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
