# Browser Session Html Interactive Tags Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_interactive_tags_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_interactive_tags_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_interactive_tags_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_interactive_tags_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Interactive Tags Specification

## Scenarios

### BrowserSession HTML interactive tag text semantics

#### shows only summary text for closed details and full content for open details

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val closed_html = "<details><summary>More</summary><p>Hidden detail</p></details>"
val open_html = "<details open><summary>More</summary><p>Visible detail</p></details>"
expect(html_to_text(closed_html)).to_equal("More")
expect(html_to_text(open_html)).to_equal("MoreVisible detail")
```

</details>

#### hides closed dialog content and exposes open dialog fallback text

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val closed_html = "<p>Before</p><dialog>Hidden dialog</dialog><p>After</p>"
val open_html = "<p>Before</p><dialog open>Visible dialog</dialog><p>After</p>"
expect(html_to_text(closed_html)).to_equal("BeforeAfter")
expect(html_to_text(open_html)).to_equal("BeforeVisible dialogAfter")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML interactive tag text semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
