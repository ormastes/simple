# Browser Session Runtime History Specification

> <details>

<!-- sdn-diagram:id=browser_session_runtime_history_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_runtime_history_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_runtime_history_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_runtime_history_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Runtime History Specification

## Scenarios

### BrowserSession runtime history

#### trims forward history before pushing a runtime navigation entry

- var session = BrowserSession new
- BrowserHistoryEntry create
- BrowserHistoryEntry create
- BrowserHistoryEntry create
- session  push runtime history entry
   - Expected: session.history.len() equals `2`
   - Expected: session.current_index equals `1`
   - Expected: session.history[0].url equals `https://example.com/first.html`
   - Expected: session.history[1].url equals `https://example.com/third.html`
   - Expected: session.history[1].source_html equals `<html><body>First</body></html>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.history = [
    BrowserHistoryEntry.create("https://example.com/first.html", "First", "<html><body>First</body></html>"),
    BrowserHistoryEntry.create("https://example.com/second.html", "Second", "<html><body>Second</body></html>"),
    BrowserHistoryEntry.create("https://example.com/stale.html", "Stale", "<html><body>Stale</body></html>")
]
session.current_index = 0
session.current_url = "https://example.com/third.html"
session.current_title = "Third"

session._push_runtime_history_entry()

expect(session.history.len()).to_equal(2)
expect(session.current_index).to_equal(1)
expect(session.history[0].url).to_equal("https://example.com/first.html")
expect(session.history[1].url).to_equal("https://example.com/third.html")
expect(session.history[1].source_html).to_equal("<html><body>First</body></html>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_runtime_history_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession runtime history

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
