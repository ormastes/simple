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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Resolves supported inline, linked, imported, and background-image stylesheet
sources. This is source-admission evidence, not complete CSS rendering.

## Scenarios

### BrowserSession HTML stylesheet sources

#### should deny every resource nested in inert templates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should deny every resource nested in inert templates
   - Expected: plan.script_blocks.len() equals `1`
   - Expected: plan.script_blocks[0].src equals `/visible.js`
   - Expected: plan.style_sources.len() equals `1`
   - Expected: plan.style_sources[0].source equals `/visible.css`
   - Expected: plan.image_sources.len() equals `1`
   - Expected: plan.image_sources[0].authored_src equals `/visible.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should deny every resource nested in inert templates")
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

- should snapshot intersected head meta CSP in document source order
- Resolve supported HTML stylesheet sources
   - Expected: plan.script_blocks.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should snapshot intersected head meta CSP in document source order")
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

- should extract inline and linked stylesheets in source order
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

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should extract inline and linked stylesheets in source order")
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

- should discover only exact single background URLs and rewrite network URLs
- Resolve supported HTML stylesheet sources
   - Expected: urls.len() equals `1`
   - Expected: urls[0] equals `../img/hero.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should discover only exact single background URLs and rewrite network URLs")
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

- should discover one URL layer inside a background shorthand
- Resolve supported HTML stylesheet sources
   - Expected: urls equals `["hero.png"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should discover one URL layer inside a background shorthand")
step("Resolve supported HTML stylesheet sources")
val urls = _css_background_image_urls(
    ".x{background:#0f8 url('hero.png') center no-repeat}"
)

expect(urls).to_equal(["hero.png"])
```

</details>

#### should rewrite only accepted background declaration URL spans

- should rewrite only accepted background declaration URL spans
- Resolve supported HTML stylesheet sources


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should rewrite only accepted background declaration URL spans")
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

- should leave unsafe background URLs unchanged and undiscovered
- Resolve supported HTML stylesheet sources
   - Expected: _css_background_image_urls(css) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should leave unsafe background URLs unchanged and undiscovered")
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

- should resolve css imports and insert expanded sources at the requested index
- Resolve supported HTML stylesheet sources
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

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should resolve css imports and insert expanded sources at the requested index")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `78e09a0c8219dcd6828675cae25282dfd96b0d0d1ed6b0608d2be9768f645cee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78e09a0c8219dcd6828675cae25282dfd96b0d0d1ed6b0608d2be9768f645cee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78e09a0c8219dcd6828675cae25282dfd96b0d0d1ed6b0608d2be9768f645cee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should deny every resource nested in inert templates' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should deny every resource nested in inert templates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should snapshot intersected head meta CSP in document source order' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should snapshot intersected head meta CSP in document source order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract inline and linked stylesheets in source order' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should extract inline and linked stylesheets in source order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl:108:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should discover only exact single background URLs and rewrite network URLs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl:129:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should discover one URL layer inside a background shorthand' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_stylesheet_sources_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should rewrite only accepted background declaration URL spans' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
