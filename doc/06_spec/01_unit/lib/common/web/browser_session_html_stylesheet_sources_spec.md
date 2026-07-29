# BrowserSession HTML stylesheet source resolution

> Resolves supported inline, linked, imported, and background-image stylesheet

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML stylesheet source resolution

Resolves supported inline, linked, imported, and background-image stylesheet

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Resolves supported inline, linked, imported, and background-image stylesheet
sources. This is source-admission evidence, not complete CSS rendering.

## Scenarios

### BrowserSession HTML stylesheet sources

#### should deny every resource nested in inert templates

- "<style> hidden{background:url
- "<div style=\"background:url
   - Expected: plan.script_blocks.len() equals `1`
   - Expected: plan.script_blocks[0].src equals `/visible.js`
   - Expected: plan.style_sources.len() equals `1`
   - Expected: plan.style_sources[0].source equals `/visible.css`
   - Expected: plan.image_sources.len() equals `1`
   - Expected: plan.image_sources[0].authored_src equals `/visible.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = browser_document_resource_plan(
    "<TEMPLATE><template><script src='/hidden.js'></script>" +
    "<style>.hidden{background:url('/hidden-style.png')}</style>" +
    "<link rel='stylesheet' href='/hidden.css'>" +
    "<img src='/hidden.png'>" +
    "<div style=\"background:url('/hidden-inline.png')\"></div>" +
    "</template></TEMPLATE>" +
    "<templateevil><script src='/visible.js'></script></templateevil>" +
    "<link rel='stylesheet' href='/visible.css'>" +
    "<img src='/visible.png'>",
    "https://safe.test/app", ""
)

expect(plan.script_blocks.len()).to_equal(1)
expect(plan.script_blocks[0].src).to_equal("/visible.js")
expect(plan.style_sources.len()).to_equal(1)
expect(plan.style_sources[0].source).to_equal("/visible.css")
expect(plan.image_sources.len()).to_equal(1)
expect(plan.image_sources[0].authored_src).to_equal("/visible.png")
```

</details>

#### should snapshot intersected head meta CSP in document source order

- Resolve supported HTML stylesheet sources
- "<style> after{background-image:url
   - Expected: plan.script_blocks.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve supported HTML stylesheet sources")
val plan = browser_document_resource_plan(
    "<html><head>" +
    "<script src='/before.js'></script>" +
    "<meta http-equiv='content-security-policy' content=\"sandbox; report-uri /r; script-src 'none'; style-src 'unsafe-inline'; img-src 'none'\">" +
    "<style>.after{background-image:url('/after.png')}</style>" +
    "<script src='/after.js'></script>" +
    "<img src='/after-image.png'>" +
    "</head></html>",
    "https://safe.test/app",
    "default-src 'self'"
)

expect(plan.script_blocks.len()).to_equal(2)
expect(plan.script_blocks[0].csp_policy).to_equal(
    "default-src 'self'"
)
expect(plan.script_blocks[1].csp_policy).to_contain(
    "script-src 'none'"
)
expect(plan.style_sources[0].csp_policy).to_contain(
    "style-src 'unsafe-inline'"
)
expect(plan.image_sources[0].csp_policy).to_contain(
    "img-src 'none'"
)
expect(plan.final_csp_policy).to_equal(
    "default-src 'self'\nscript-src 'none'; style-src 'unsafe-inline'; img-src 'none'"
)
```

</details>

#### should extract inline and linked stylesheets in source order

- Resolve supported HTML stylesheet sources
   - Expected: sources.len() equals `4`
   - Expected: sources[0].kind equals `external`
   - Expected: sources[0].source equals `/first.css`
   - Expected: sources[1].kind equals `inline`
   - Expected: sources[1].source equals `body { color: red; }`
   - Expected: sources[2].kind equals `external`
   - Expected: sources[2].source equals `/last.css`
   - Expected: sources[3].kind equals `inline`
   - Expected: sources[3].source equals `.last { color: blue; }`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve supported HTML stylesheet sources")
val html = "<html><head><link rel=\"stylesheet\" href=\"/first.css\"><style>body { color: red; }</style><link rel=\"icon\" href=\"/favicon.ico\"><link rel=\"preload stylesheet\" href=\"/last.css\"><style>.last { color: blue; }</style></head></html>"

val sources = extract_stylesheet_sources(html)

expect(sources.len()).to_equal(4)
expect(sources[0].kind).to_equal("external")
expect(sources[0].source).to_equal("/first.css")
expect(sources[1].kind).to_equal("inline")
expect(sources[1].source).to_equal("body { color: red; }")
expect(sources[2].kind).to_equal("external")
expect(sources[2].source).to_equal("/last.css")
expect(sources[3].kind).to_equal("inline")
expect(sources[3].source).to_equal(".last { color: blue; }")
```

</details>

#### should discover only exact single background URLs and rewrite network URLs

- Resolve supported HTML stylesheet sources
   - Expected: urls.len() equals `1`
   - Expected: urls[0] equals `../img/hero.png`
- "url
- "background: url


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve supported HTML stylesheet sources")
val css = ".hero { background: #0f8 url('../img/hero.png') center no-repeat; } .multi { background: url('a.png'), url('b.png'); } .data { background-image: url(data:image/png;base64,abcd); }"

val urls = _css_background_image_urls(css)
val rewritten = _rewrite_css_background_image_urls(
    css, "https://example.test/assets/css/app.css"
)

expect(urls.len()).to_equal(1)
expect(urls[0]).to_equal("../img/hero.png")
expect(rewritten).to_contain(
    "url(\"https://example.test/assets/img/hero.png\")"
)
expect(rewritten).to_contain("url(data:image/png;base64,abcd)")
expect(rewritten).to_contain(
    "background: url('a.png'), url('b.png')"
)
```

</details>

#### should discover one URL layer inside a background shorthand

- Resolve supported HTML stylesheet sources
- " x{background:#0f8 url
   - Expected: urls equals `["hero.png"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve supported HTML stylesheet sources")
val urls = _css_background_image_urls(
    ".x{background:#0f8 url('hero.png') center no-repeat}"
)

expect(urls).to_equal(["hero.png"])
```

</details>

#### should rewrite only accepted background declaration URL spans

- Resolve supported HTML stylesheet sources
- "@import url


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve supported HTML stylesheet sources")
val css = "@import url('theme.css');@font-face{font-family:x;src:url('font.woff2')}.hero{background:url('hero.png') center no-repeat}"

val rewritten = _rewrite_css_background_image_urls(
    css, "https://example.test/css/app.css"
)

expect(rewritten).to_equal(
    "@import url('theme.css');@font-face{font-family:x;src:url('font.woff2')}.hero{background:url(\"https://example.test/css/hero.png\") center no-repeat}"
)
```

</details>

#### should leave unsafe background URLs unchanged and undiscovered

- Resolve supported HTML stylesheet sources
- " quote{background:url
- " slash{background:url
- " control{background:url
- " tag{background:url
- " interpolation{background:url
   - Expected: _css_background_image_urls(css) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve supported HTML stylesheet sources")
val quote = 34.to_char()
val slash = 92.to_char()
val control = 10.to_char()
val interpolation = 123.to_char() + "host" + 125.to_char()
val css = (
    ".quote{background:url('bad" + quote + "name.png')}" +
    ".slash{background:url('bad" + slash + "name.png')}" +
    ".control{background:url('bad" + control + "name.png')}" +
    ".tag{background:url('</style>.png')}" +
    ".interpolation{background:url('" + interpolation + ".png')}"
)

expect(_css_background_image_urls(css)).to_equal([])
expect(_rewrite_css_background_image_urls(
    css, "https://example.test/css/app.css"
)).to_equal(css)
```

</details>

#### should resolve css imports and insert expanded sources at the requested index

- Resolve supported HTML stylesheet sources
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

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve supported HTML stylesheet sources")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
