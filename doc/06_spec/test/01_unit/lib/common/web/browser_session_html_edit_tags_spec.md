# Browser Session Html Edit Tags Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_edit_tags_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_edit_tags_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_edit_tags_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_edit_tags_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Edit Tags Specification

## Scenarios

### BrowserSession HTML edit tag text semantics

#### marks inserted and deleted text in plain text extraction

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<p>Before <del cite='/old'>old</del><ins datetime='2026-06-06'>new</ins> after</p>"
expect(html_to_text(html)).to_equal("Before [-old][+new] after")
```

</details>

#### keeps nested inline text inside edit annotations

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<del><strong>removed</strong> text</del><ins><em>added</em> text</ins>"
expect(html_to_text(html)).to_equal("[-removed text][+added text]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_edit_tags_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML edit tag text semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
