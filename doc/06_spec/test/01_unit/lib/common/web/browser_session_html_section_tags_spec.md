# Browser Session Html Section Tags Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_section_tags_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_section_tags_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_section_tags_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_section_tags_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Section Tags Specification

## Scenarios

### BrowserSession HTML section and heading tag text semantics

#### separates body headings hgroup and address into readable lines

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<body><hgroup><h1>Title</h1><p>Subtitle</p></hgroup><h2>Chapter</h2><h3>Section</h3><h4>Topic</h4><h5>Detail</h5><h6>Leaf</h6><address>Contact</address></body>"
expect(html_to_text(html)).to_equal("Title\nSubtitle\nChapter\nSection\nTopic\nDetail\nLeaf\nContact")
```

</details>

#### keeps adjacent headings from collapsing into one token

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<h1>One</h1><h2>Two</h2><h3>Three</h3><h4>Four</h4><h5>Five</h5><h6>Six</h6>"
expect(html_to_text(html)).to_equal("One\nTwo\nThree\nFour\nFive\nSix")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_section_tags_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML section and heading tag text semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
