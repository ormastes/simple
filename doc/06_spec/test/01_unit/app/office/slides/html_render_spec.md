# Html Render Specification

> <details>

<!-- sdn-diagram:id=html_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_render_spec -> std
html_render_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Render Specification

## Scenarios

### slide HTML render: title slide

#### wraps the slide in a styled <section>

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_slide_html(title_slide("s1", "My Talk", "A subtitle"))
expect(html).to_start_with("<section class=\"slide\"")
expect(html).to_contain("position: relative; width: 960px; height: 540px;")
expect(html).to_end_with("</section>")
```

</details>

#### styles the title as slide_title (bold, centered, 2.5em)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_slide_html(title_slide("s1", "My Talk", "A subtitle"))
expect(html).to_contain("class=\"slide_title\"")
expect(html).to_contain("font-size: 2.5em;")
expect(html).to_contain("text-align: center;")
expect(html).to_contain(">My Talk</div>")
```

</details>

#### styles the second element as slide_subtitle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_slide_html(title_slide("s1", "My Talk", "A subtitle"))
expect(html).to_contain("class=\"slide_subtitle\"")
expect(html).to_contain(">A subtitle</div>")
```

</details>

### slide HTML render: content slide
_A content slide styles its non-title elements as slide_body._

#### styles the body element as slide_body

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_slide_html(content_slide("s2", "Agenda", "First point"))
expect(html).to_contain("class=\"slide_title\"")
expect(html).to_contain("class=\"slide_body\"")
expect(html).to_contain(">First point</div>")
```

</details>

#### positions slide elements with deterministic CSS boxes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_slide_html(content_slide("s2", "Agenda", "First point"))
expect(html).to_contain("data-slide-id=\"s2\"")
expect(html).to_contain("data-element-id=\"s2_title\" data-kind=\"text\"")
expect(html).to_contain("data-element-id=\"s2_body\" data-kind=\"text\"")
expect(html).to_contain("left: 50px; top: 30px; width: 860px; height: 60px;")
expect(html).to_contain("left: 50px; top: 110px; width: 860px; height: 400px;")
```

</details>

#### escapes text and sanitizes CSS colors in malformed presentation input

- kind: SlideElementKind TextBox
- kind: SlideElementKind ShapeEl
   - Expected: slide_safe_css_color("#0F766E", "#ffffff") equals `#0F766E`
   - Expected: slide_safe_css_color("#fff; color:red", "#ffffff") equals `#ffffff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsafe = Slide(
    id: "unsafe",
    layout: SlideLayout.TitleContent,
    elements: [
        SlideElement(
            id: "title",
            kind: SlideElementKind.TextBox(content: "<b onclick='x'>Title</b>"),
            x: -10,
            y: -20,
            width: 300,
            height: 60
        ),
        SlideElement(
            id: "shape",
            kind: SlideElementKind.ShapeEl(shape_type: "rect<script>", fill_color: "red; background:url(js)"),
            x: 20,
            y: 90,
            width: 200,
            height: 80
        )
    ],
    notes: "",
    background: "#fff; color:red"
)
val html = render_slide_html(unsafe)
expect(slide_safe_css_color("#0F766E", "#ffffff")).to_equal("#0F766E")
expect(slide_safe_css_color("#fff; color:red", "#ffffff")).to_equal("#ffffff")
expect(html).to_contain("background: #ffffff;")
expect(html).to_contain("&lt;b onclick=&#39;x&#39;&gt;Title&lt;/b&gt;")
expect(html).to_contain("[rect&lt;script&gt;]")
expect(html).to_contain("data-element-id=\"shape\" data-kind=\"shape\"")
expect(html).to_contain("background: #E5E7EB;")
expect(html).to_contain("left: 0px; top: 0px;")
```

</details>

### slide HTML render: markdown source

#### renders markdown headings as slide pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_ppt_markdown_html("---\nlayout: presentation\n---\n\n## Slide One\n\nBody\n\n## Slide Two\n\nNext")
expect(html).to_start_with("<section class=\"md-ppt-deck\"")
expect(html).to_contain("data-layout=\"presentation\"")
expect(html).to_contain("data-format=\"markdown-ppt\"")
expect(html).to_contain("data-format-name=\"Impress Markdown\"")
expect(html).to_contain("data-slide-count=\"2\"")
expect(html).to_contain("data-slide=\"1\" data-source-line=\"1\"")
expect(html).to_contain("<h2>Slide One</h2>")
expect(html).to_contain("<p>Body</p>")
expect(html).to_contain("data-slide=\"2\" data-source-line=\"5\"")
```

</details>

#### drops unsafe markdown slide css class tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_ppt_markdown_html("## Slide @deck @bad&quot;onclick=1 @accent_1\n\nBody")
expect(html).to_contain("class=\"md-ppt-slide md-css-deck md-css-accent_1\"")
expect(html.contains("md-css-bad")).to_be(false)
```

</details>

#### drops quoted markdown slide css class tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_ppt_markdown_html("## Slide @deck @\" onclick=\"alert(1) @accent_1\n\nBody")
expect(html).to_contain("class=\"md-ppt-slide md-css-deck md-css-accent_1\"")
expect(html.contains("onclick=\"alert(1)")).to_be(false)
```

</details>

#### renders and sanitizes inline links in PPT markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_ppt_markdown_html("## Intro\n\nSee [Docs](docs.md?a=1&b=2)\n\nNo [Script](javascript:alert(1))")
expect(html).to_contain("<a href=\"docs.md?a=1&amp;b=2\">Docs</a>")
expect(html).to_contain("<a href=\"#\">Script</a>")
```

</details>

#### escapes slide markdown content before HTML rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_ppt_markdown_html("## <script>alert(1)</script>\n\nBody")
expect(html).to_contain("&lt;script&gt;alert(1)&lt;/script&gt;")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slides/html_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- slide HTML render: title slide
- slide HTML render: content slide
- slide HTML render: markdown source

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
