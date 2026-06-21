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
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Render Specification

## Scenarios

### slide HTML render: title slide

#### wraps the slide in a styled <section>

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_slide_html(title_slide("s1", "My Talk", "A subtitle"))
expect(html).to_start_with("<section class=\"slide\"")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
