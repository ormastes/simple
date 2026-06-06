# Browser Session Html Metadata Tags Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_metadata_tags_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_metadata_tags_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_metadata_tags_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_metadata_tags_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Metadata Tags Specification

## Scenarios

### BrowserSession HTML metadata tag text semantics

#### keeps document metadata out of visible text extraction

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<!DOCTYPE html><html><head><title>Hidden title</title><base href='https://example.com/'><link rel='stylesheet' href='site.css'><meta name='description' content='Hidden meta'><style>body { color: red; }</style></head><body>Visible body</body></html>"
expect(html_to_text(html)).to_equal("Visible body")
```

</details>

#### keeps standalone title and style contents hidden

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<title>Hidden title</title><style>.hidden { display: none; }</style><p>Visible paragraph</p>"
expect(html_to_text(html)).to_equal("Visible paragraph")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_metadata_tags_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML metadata tag text semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
