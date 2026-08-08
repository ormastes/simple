# BrowserSession HTML scripting text projection

> Projects script and noscript content according to the active runtime. This is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML scripting text projection

Projects script and noscript content according to the active runtime. This is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Projects script and noscript content according to the active runtime. This is
visible-document evidence, not full JavaScript or pixel-rendering coverage.

## Scenarios

### BrowserSession HTML scripting tag semantics

#### should hide noscript fallback from visible rendering when scripting is enabled

- Project supported HTML semantics to visible text
- var session = BrowserSession new
- Ok
   - Expected: session.current_body_html does not contain `Fallback body`
   - Expected: session.render_html_document() does not contain `Fallback body`
- Err
   - Expected: "unexpected open error: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
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

#### should run script content and hide noscript fallback when scripting is enabled

- Project supported HTML semantics to visible text
- var session = BrowserSession new
- Ok
   - Expected: session.current_body_html equals `Scripted body`
   - Expected: session.current_body_html does not contain `Fallback body`
   - Expected: session.render_html_document() does not contain `Fallback body`
- Err
   - Expected: "unexpected open error: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
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

#### should ignore script content and keep noscript fallback visible when runtime is disabled

- Project supported HTML semantics to visible text
- var session = BrowserSession new without runtime
- Ok
   - Expected: session.current_body_html does not contain `Scripted body`
- Err
   - Expected: "unexpected open error: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
