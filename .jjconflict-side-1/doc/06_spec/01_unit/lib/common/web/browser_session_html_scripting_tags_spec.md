# Browser Session Html Scripting Tags Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_scripting_tags_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_scripting_tags_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_scripting_tags_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_scripting_tags_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Scripting Tags Specification

## Scenarios

### BrowserSession HTML scripting tag semantics

#### hides noscript fallback from visible rendering when scripting is enabled

- var session = BrowserSession new
- Ok
   - Expected: session.current_body_html does not contain `Fallback body`
   - Expected: session.render_html_document() does not contain `Fallback body`
- Err
   - Expected: "unexpected open error: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_html(
    "https://example.com/noscript-enabled",
    "<!DOCTYPE html><html><head><title>NoScript Enabled</title></head><body><p>Visible</p><noscript>Fallback body</noscript></body></html>"
)
match result:
    Ok(_):
        expect(session.source_html).to_contain("<noscript>Fallback body</noscript>")
        expect(session.current_body_html).to_contain("<p>Visible</p>")
        expect(session.current_body_html.contains("Fallback body")).to_equal(false)
        expect(session.render_html_document().contains("Fallback body")).to_equal(false)
    Err(e):
        expect("unexpected open error: {e}").to_equal("")
```

</details>

#### runs script content and hides noscript fallback when scripting is enabled

- var session = BrowserSession new
- Ok
   - Expected: session.current_body_html equals `Scripted body`
   - Expected: session.current_body_html does not contain `Fallback body`
   - Expected: session.render_html_document() does not contain `Fallback body`
- Err
   - Expected: "unexpected open error: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val result = session.open_html(
    "https://example.com/scripted",
    "<!DOCTYPE html><html><head><title>Script Tags</title></head><body><p>Before</p><script>document.body.textContent = 'Scripted body';</script><noscript>Fallback body</noscript></body></html>"
)
match result:
    Ok(_):
        expect(session.source_html).to_contain("<noscript>Fallback body</noscript>")
        expect(session.current_body_html).to_equal("Scripted body")
        expect(session.current_body_html.contains("Fallback body")).to_equal(false)
        expect(session.render_html_document().contains("Fallback body")).to_equal(false)
    Err(e):
        expect("unexpected open error: {e}").to_equal("")
```

</details>

#### ignores script content and keeps noscript fallback visible when runtime is disabled

- var session = BrowserSession new without runtime
- Ok
   - Expected: session.current_body_html does not contain `Scripted body`
- Err
   - Expected: "unexpected open error: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new_without_runtime()
val result = session.open_html(
    "https://example.com/noscript",
    "<!DOCTYPE html><html><head><title>No Script Tags</title></head><body><p>Before</p><script>document.body.textContent = 'Scripted body';</script><noscript>Fallback body</noscript></body></html>"
)
match result:
    Ok(_):
        expect(session.current_body_html).to_contain("<p>Before</p>")
        expect(session.current_body_html).to_contain("<noscript>Fallback body</noscript>")
        expect(session.current_body_html.contains("Scripted body")).to_equal(false)
        expect(session.warnings).to_contain("scripts are ignored when BrowserSession runtime is disabled")
    Err(e):
        expect("unexpected open error: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML scripting tag semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
