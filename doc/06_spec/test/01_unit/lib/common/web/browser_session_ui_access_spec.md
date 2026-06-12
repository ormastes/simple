# Browser Session Ui Access Specification

> <details>

<!-- sdn-diagram:id=browser_session_ui_access_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_ui_access_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_ui_access_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_ui_access_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Ui Access Specification

## Scenarios

### BrowserSession UI access

#### strips inline tags from link labels in source order

- var session = BrowserSession new
   - Expected: _link_text(snapshot, "link_0") equals `Alpha Beta Gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.current_url = "https://example.com/base/index.html"
session.current_title = "Links"
session.current_body_html = "<a href=\"next.html\">Alpha <strong>Beta</strong> <span>Gamma</span></a>"

val snapshot = session.ui_access_snapshot()
expect(_link_text(snapshot, "link_0")).to_equal("Alpha Beta Gamma")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_ui_access_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession UI access

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
