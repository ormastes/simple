# Browser Session Html Text Level Tags Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_text_level_tags_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_text_level_tags_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_text_level_tags_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_text_level_tags_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Text Level Tags Specification

## Scenarios

### BrowserSession HTML text-level tag semantics

#### preserves text content across common text-level formatting tags

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<p><em>em</em><strong>strong</strong><small>small</small><s>s</s><cite>cite</cite><q>quote</q><dfn>dfn</dfn><abbr>abbr</abbr><data value='7'>data</data><time datetime='2026-06-06'>time</time><code>code</code><var>var</var><samp>samp</samp><kbd>kbd</kbd><sub>sub</sub><sup>sup</sup><i>i</i><b>b</b><u>u</u><mark>mark</mark><bdi>bdi</bdi><bdo dir='rtl'>bdo</bdo><span>span</span></p>"
expect(html_to_text(html)).to_equal("emstrongsmallscitequotedfnabbrdatatimecodevarsampkbdsubsupibumarkbdibdospan")
```

</details>

#### maps br to a visible line break and wbr to an optional zero-width break

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<p>alpha<br>beta<wbr>gamma</p>"
expect(html_to_text(html)).to_equal("alpha\nbetagamma")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_text_level_tags_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML text-level tag semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
