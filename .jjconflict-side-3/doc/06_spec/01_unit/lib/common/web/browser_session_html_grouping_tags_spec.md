# BrowserSession HTML grouping text projection

> Projects the supported grouping and list semantics to visible text. This is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML grouping text projection

Projects the supported grouping and list semantics to visible text. This is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Projects the supported grouping and list semantics to visible text. This is
focused text-projection evidence, not complete HTML parsing or rendering.

## Scenarios

### BrowserSession HTML grouping tag text semantics

#### should preserve paragraph pre blockquote figure and div text

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Paragraph\n Pre text QuoteFigure bodyCaption`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<div><p>Paragraph</p><hr><pre> Pre text </pre><blockquote>Quote</blockquote><figure><div>Figure body</div><figcaption>Caption</figcaption></figure></div>"
expect(html_to_text(html)).to_equal("Paragraph\n Pre text QuoteFigure bodyCaption")
```

</details>

#### should separate ordered unordered and menu list items

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `One\nTwo\nAlpha\nBeta\nAction\nMore`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<ol><li>One</li><li>Two</li></ol><ul><li>Alpha</li><li>Beta</li></ul><menu><li>Action</li><li>More</li></menu>"
expect(html_to_text(html)).to_equal("One\nTwo\nAlpha\nBeta\nAction\nMore")
```

</details>

#### should separate definition list terms and descriptions

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Term: Description\nNext: More`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<dl><dt>Term</dt><dd>Description</dd><dt>Next</dt><dd>More</dd></dl>"
expect(html_to_text(html)).to_equal("Term: Description\nNext: More")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
