# Browser Session Html Stylesheet Sources Specification

> <details>

<!-- sdn-diagram:id=browser_session_html_stylesheet_sources_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_stylesheet_sources_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_stylesheet_sources_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_stylesheet_sources_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Stylesheet Sources Specification

## Scenarios

### BrowserSession HTML stylesheet sources

#### extracts inline and linked stylesheets in source order

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { color: red; }</style><link rel=\"preload stylesheet\" href=\"/app.css\"><link rel=\"icon\" href=\"/favicon.ico\"></head></html>"

val sources = extract_stylesheet_sources(html)

expect(sources.len()).to_equal(2)
expect(sources[0].kind).to_equal("inline")
expect(sources[0].source).to_equal("body { color: red; }")
expect(sources[1].kind).to_equal("external")
expect(sources[1].source).to_equal("/app.css")
```

</details>

#### resolves css imports and inserts expanded sources at the requested index

- BrowserStylesheetSource external
- BrowserStylesheetSource inline
   - Expected: imports.len() equals `2`
   - Expected: imports[0].source equals `https://example.com/assets/base.css`
   - Expected: imports[1].source equals `https://example.com/assets/app/theme.css`
   - Expected: cleaned equals `.main { display: block; }`
   - Expected: combined.len() equals `4`
   - Expected: combined[0].source equals `first.css`
   - Expected: combined[1].source equals `https://example.com/assets/base.css`
   - Expected: combined[2].source equals `https://example.com/assets/app/theme.css`
   - Expected: combined[3].source equals `.local {}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = "@import url('../base.css');\n@import \"theme.css\";\n.main { display: block; }"

val imports = extract_css_import_sources("https://example.com/assets/app/main.css", css)
val cleaned = strip_css_imports(css).trim()
val existing = [
    BrowserStylesheetSource.external("first.css"),
    BrowserStylesheetSource.inline(".local {}")
]
val combined = insert_stylesheet_sources(existing, 1, imports)

expect(imports.len()).to_equal(2)
expect(imports[0].source).to_equal("https://example.com/assets/base.css")
expect(imports[1].source).to_equal("https://example.com/assets/app/theme.css")
expect(cleaned).to_equal(".main { display: block; }")
expect(combined.len()).to_equal(4)
expect(combined[0].source).to_equal("first.css")
expect(combined[1].source).to_equal("https://example.com/assets/base.css")
expect(combined[2].source).to_equal("https://example.com/assets/app/theme.css")
expect(combined[3].source).to_equal(".local {}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML stylesheet sources

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
