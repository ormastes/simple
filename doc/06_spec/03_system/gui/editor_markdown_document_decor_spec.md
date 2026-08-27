# Editor Markdown Document Decor Specification

> Tests covering markdown document decoration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Markdown Document Decor Specification

## Scenarios

### markdown document decoration

#### parses page view, header, footer, and css file from frontmatter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses page view, header, footer, and css file from frontmatter
   - Expected: decor.page_view is true
   - Expected: decor.header equals `Release Note`
   - Expected: decor.footer equals `Page 1`
   - Expected: decor.css_file equals `./modern.css`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses page view, header, footer, and css file from frontmatter")
val decor = md_document_decor_parse("---\npage_view: true\nheader: Release Note\nfooter: Page 1\ncss_file: \"./modern.css\"\n---\n# Title")
expect(decor.page_view).to_equal(true)
expect(decor.header).to_equal("Release Note")
expect(decor.footer).to_equal("Page 1")
expect(decor.css_file).to_equal("./modern.css")
```

</details>

#### collects inline css fences

- collects inline css fences


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collects inline css fences")
val decor = md_document_decor_parse("# Title\n\n```css\n.md-page { color: red; }\n```\n\nBody")
expect(decor.inline_css).to_contain(".md-page")
expect(decor.inline_css).to_contain("color: red")
```

</details>

#### removes frontmatter and css fences from document body

- removes frontmatter and css fences from document body
   - Expected: body equals `# Title\n\nBody`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes frontmatter and css fences from document body")
val body = md_document_body_without_decor("---\npage_view: true\n---\n\n# Title\n\n```css\n.hidden {}\n```\n\nBody")
expect(body).to_equal("# Title\n\nBody")
```

</details>

#### adapts css fences as markdown css blocks

- adapts css fences as markdown css blocks
   - Expected: model.block_count() equals `1`
   - Expected: model.block_at(0).kind equals `md_css`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adapts css fences as markdown css blocks")
val model = BlockModel.from_markdown("```css\n.note { color: blue; }\n```")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("md_css")
```

</details>

#### renders css fences in TUI preview as a compact marker

- renders css fences in TUI preview as a compact marker
   - Expected: rendered.len() equals `1`
   - Expected: rendered[0] contains `[css]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders css fences in TUI preview as a compact marker")
val block = RenderBlock(id: 1, kind: "md_css", from_line: 0, to_line: 2, content: "```css\n.x {}\n```", rendered_lines: ["```css", ".x {}", "```"], status: "ok")
val rendered = md_render_block(block)
expect(rendered.len()).to_equal(1)
expect(rendered[0].contains("[css]")).to_equal(true)
```

</details>

#### renders document page view with header, footer, external css, inline css, and body

- renders document page view with header, footer, external css, inline css, and body
   - Expected: html does not contain `page_view: true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders document page view with header, footer, external css, inline css, and body")
val html = gui_render_markdown_document("---\npage_view: true\nheader: Release Note\nfooter: Page 1\ncss_file: ./modern.css\n---\n\n# Title\n\n```css\n.md-page { color: red; }\n```\n\nBody")
expect(html).to_contain("class=\"md-document page-view\"")
expect(html).to_contain("data-page-view=\"true\"")
expect(html).to_contain("class=\"md-page-header\"")
expect(html).to_contain("Release Note")
expect(html).to_contain("class=\"md-page-footer\"")
expect(html).to_contain("Page 1")
expect(html).to_contain("href=\"./modern.css\"")
expect(html).to_contain("class=\"md-inline-css\"")
expect(html).to_contain("md-page")
expect(html).to_contain("<h1>Title</h1>")
expect(html).to_contain("<p>Body</p>")
expect(html.contains("page_view: true")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_markdown_document_decor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering markdown document decoration.
- markdown document decoration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eac0d199003cc3ad2f7b7a49f04e0de4ec0cb4f52b026146b4500f667303193a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eac0d199003cc3ad2f7b7a49f04e0de4ec0cb4f52b026146b4500f667303193a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eac0d199003cc3ad2f7b7a49f04e0de4ec0cb4f52b026146b4500f667303193a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/gui/editor_markdown_document_decor_spec.spl
mirror: doc/06_spec/03_system/gui/editor_markdown_document_decor_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_markdown_document_decor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_markdown_document_decor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_markdown_document_decor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/editor_markdown_document_decor_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses page view, header, footer, and css file from frontmatter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_markdown_document_decor_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects inline css fences' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_markdown_document_decor_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes frontmatter and css fences from document body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
