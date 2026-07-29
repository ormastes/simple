# BrowserSession HTML metadata text projection

> Keeps supported document metadata outside visible text projection. This is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML metadata text projection

Keeps supported document metadata outside visible text projection. This is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_metadata_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Keeps supported document metadata outside visible text projection. This is
focused visibility evidence, not complete metadata processing or rendering.

## Scenarios

### BrowserSession HTML metadata tag text semantics

#### should keep document metadata out of visible text extraction

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Visible body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<!DOCTYPE html><html><head><title>Hidden title</title><base href='https://example.com/'><link rel='stylesheet' href='site.css'><meta name='description' content='Hidden meta'><style>body { color: red; }</style></head><body>Visible body</body></html>"
expect(html_to_text(html)).to_equal("Visible body")
```

</details>

#### should keep standalone title and style contents hidden

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Visible paragraph`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<title>Hidden title</title><style>.hidden { display: none; }</style><p>Visible paragraph</p>"
expect(html_to_text(html)).to_equal("Visible paragraph")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
