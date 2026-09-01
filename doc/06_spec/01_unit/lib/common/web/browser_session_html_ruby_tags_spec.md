# Browser Session Html Ruby Tags Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_ruby_tags_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_ruby_tags_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_ruby_tags_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_ruby_tags_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Ruby Tags Specification

## Scenarios

### BrowserSession HTML ruby tag text semantics

#### renders ruby annotations without leaking rp fallback markers twice

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<ruby>漢<rp>(</rp><rt>kan</rt><rp>)</rp></ruby>"
expect(html_to_text(html)).to_equal("漢(kan)")
```

</details>

#### keeps adjacent ruby annotations readable without rp fallback tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<ruby>東<rt>east</rt></ruby><ruby>京<rt>capital</rt></ruby>"
expect(html_to_text(html)).to_equal("東(east)京(capital)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML ruby tag text semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
