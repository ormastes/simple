# Browser Session Html Grouping Tags Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_grouping_tags_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_grouping_tags_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_grouping_tags_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_grouping_tags_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Grouping Tags Specification

## Scenarios

### BrowserSession HTML grouping tag text semantics

#### preserves paragraph pre blockquote figure and div text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<div><p>Paragraph</p><hr><pre> Pre text </pre><blockquote>Quote</blockquote><figure><div>Figure body</div><figcaption>Caption</figcaption></figure></div>"
expect(html_to_text(html)).to_equal("Paragraph\n Pre text QuoteFigure bodyCaption")
```

</details>

#### separates ordered unordered and menu list items

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<ol><li>One</li><li>Two</li></ol><ul><li>Alpha</li><li>Beta</li></ul><menu><li>Action</li><li>More</li></menu>"
expect(html_to_text(html)).to_equal("One\nTwo\nAlpha\nBeta\nAction\nMore")
```

</details>

#### separates definition list terms and descriptions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<dl><dt>Term</dt><dd>Description</dd><dt>Next</dt><dd>More</dd></dl>"
expect(html_to_text(html)).to_equal("Term: Description\nNext: More")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML grouping tag text semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
