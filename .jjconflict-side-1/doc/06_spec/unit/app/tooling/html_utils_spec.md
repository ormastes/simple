# Html Utils Specification

> Tests covering HTML Utilities, HTML Escaping, Basic HTML Elements, Document Structure, Head Elements, Text Elements, Formatting Elements, Link Elements, Image Elements, List Elements, Table Elements, Form Elements, Semantic Elements, Builder Pattern, Common Patterns.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Utils Specification

## Scenarios

### HTML Utilities

### HTML Escaping

#### escapes ampersand

- escapes ampersand


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes ampersand")
expect escape_html("A & B") == "A &amp; B"
```

</details>

#### escapes less than

- escapes less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes less than")
expect escape_html("A < B") == "A &lt; B"
```

</details>

#### escapes greater than

- escapes greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes greater than")
expect escape_html("A > B") == "A &gt; B"
```

</details>

#### escapes quotes

- escapes quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes quotes")
expect escape_html("Say \"hello\"") == "Say &quot;hello&quot;"
```

</details>

#### unescapes HTML entities

- unescapes HTML entities


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unescapes HTML entities")
expect unescape_html("A &amp; B") == "A & B"
expect unescape_html("A &lt; B") == "A < B"
```

</details>

### Basic HTML Elements

#### creates simple tag

- creates simple tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates simple tag")
val result = tag(name="p", content="Hello")
expect result == "<p>Hello</p>"
```

</details>

#### creates self-closing tag

- creates self-closing tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates self-closing tag")
val result = self_closing_tag("br")
expect result == "<br />"
```

</details>

#### creates tag with attributes

- creates tag with attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates tag with attributes")
val result = tag_with_attrs(name="a", attrs=[("href", "/home")], content="Home")
expect result.contains("href=\"/home\"")
expect result.contains(">Home</a>")
```

</details>

### Document Structure

#### creates HTML document

- creates HTML document


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates HTML document")
val result = html_document(head="<title>Test</title>", body="<p>Content</p>")
expect result.contains("<!DOCTYPE html>")
expect result.contains("<html>")
expect result.contains("<head>")
```

</details>

#### creates HTML5 document with lang

- creates HTML5 document with lang


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates HTML5 document with lang")
val result = html5_document(lang="en", head="<title>Test</title>", body="<p>Content</p>")
expect result.contains("lang=\"en\"")
expect result.contains("<!DOCTYPE html>")
```

</details>

#### generates doctype

- generates doctype


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates doctype")
expect doctype_html5() == "<!DOCTYPE html>"
```

</details>

### Head Elements

#### creates title

- creates title


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates title")
expect title("My Page") == "<title>My Page</title>"
```

</details>

#### creates meta tag

- creates meta tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates meta tag")
val result = meta(name="description", content="Page description")
expect result.contains("name=\"description\"")
expect result.contains("content=\"Page description\"")
```

</details>

#### creates charset meta

- creates charset meta


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates charset meta")
val result = meta_charset("UTF-8")
expect result.contains("charset=\"UTF-8\"")
```

</details>

#### creates stylesheet link

- creates stylesheet link


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates stylesheet link")
val result = link_stylesheet("style.css")
expect result.contains("rel=\"stylesheet\"")
expect result.contains("href=\"style.css\"")
```

</details>

### Text Elements

#### creates headings

- creates headings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates headings")
expect h1("Title") == "<h1>Title</h1>"
expect h2("Subtitle") == "<h2>Subtitle</h2>"
```

</details>

#### creates paragraph

- creates paragraph


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates paragraph")
expect p("Paragraph") == "<p>Paragraph</p>"
```

</details>

#### creates div

- creates div


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates div")
expect div("<p>Content</p>") == "<div><p>Content</p></div>"
```

</details>

#### creates span

- creates span


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates span")
expect span("Text") == "<span>Text</span>"
```

</details>

### Formatting Elements

#### creates strong

- creates strong


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates strong")
expect strong("Bold") == "<strong>Bold</strong>"
```

</details>

#### creates em

- creates em


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates em")
expect em("Italic") == "<em>Italic</em>"
```

</details>

#### creates code

- creates code


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates code")
expect code("x = 1") == "<code>x = 1</code>"
```

</details>

#### creates br

- creates br


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates br")
expect br() == "<br />"
```

</details>

#### creates hr

- creates hr


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates hr")
expect hr() == "<hr />"
```

</details>

### Link Elements

#### creates anchor

- creates anchor


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates anchor")
val result = a(href="/page", txt="Click here")
expect result.contains("href=\"/page\"")
expect result.contains(">Click here</a>")
```

</details>

#### creates external link

- creates external link


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates external link")
val result = a_external(href="https://example.com", txt="Example")
expect result.contains("target=\"_blank\"")
```

</details>

### Image Elements

#### creates image

- creates image


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates image")
val result = img(src="pic.jpg", alt="A picture")
expect result.contains("src=\"pic.jpg\"")
expect result.contains("alt=\"A picture\"")
```

</details>

### List Elements

#### creates unordered list

- creates unordered list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates unordered list")
val result = ul(["Item 1", "Item 2", "Item 3"])
expect result.contains("<ul>")
expect result.contains("<li>Item 1</li>")
expect result.contains("</ul>")
```

</details>

#### creates ordered list

- creates ordered list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates ordered list")
val result = ol(["First", "Second", "Third"])
expect result.contains("<ol>")
expect result.contains("<li>First</li>")
expect result.contains("</ol>")
```

</details>

#### creates list item

- creates list item


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates list item")
expect li("Item") == "<li>Item</li>"
```

</details>

### Table Elements

#### creates table

- creates table


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates table")
val result = table(["Name", "Age"], [["Alice", "30"], ["Bob", "25"]])
expect result.contains("<table>")
expect result.contains("<thead>")
expect result.contains("<th>Name</th>")
expect result.contains("<tbody>")
expect result.contains("<td>Alice</td>")
expect result.contains("</table>")
```

</details>

#### creates table row

- creates table row


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates table row")
val result = tr(["A", "B", "C"])
expect result.contains("<tr>")
expect result.contains("<td>A</td>")
expect result.contains("</tr>")
```

</details>

#### creates th and td

- creates th and td


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates th and td")
expect th("Header") == "<th>Header</th>"
expect td("Data") == "<td>Data</td>"
```

</details>

### Form Elements

#### creates form

- creates form


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates form")
val result = form(action="/submit", method="POST", content="<input>")
expect result.contains("action=\"/submit\"")
expect result.contains("method=\"POST\"")
```

</details>

#### creates text input

- creates text input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates text input")
val result = input_text(name="email", default_val="user@example.com")
expect result.contains("type=\"text\"")
expect result.contains("name=\"email\"")
```

</details>

#### creates submit button

- creates submit button


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates submit button")
val result = button_submit("Send")
expect result.contains("type=\"submit\"")
```

</details>

### Semantic Elements

#### creates header

- creates header


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates header")
expect header("<h1>Title</h1>") == "<header><h1>Title</h1></header>"
```

</details>

#### creates footer

- creates footer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates footer")
expect footer("<p>Copyright</p>") == "<footer><p>Copyright</p></footer>"
```

</details>

#### creates nav

- creates nav


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates nav")
expect nav("<ul><li>Home</li></ul>") == "<nav><ul><li>Home</li></ul></nav>"
```

</details>

#### creates main

- creates main


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates main")
expect main_element("<p>Content</p>") == "<main><p>Content</p></main>"
```

</details>

### Builder Pattern

#### builds basic HTML

- builds basic HTML


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds basic HTML")
var builder = HtmlBuilder.create()
builder.add_heading(level=1, txt="Title")
builder.add_paragraph("Content")
val result = builder.build()
expect result.contains("<h1>Title</h1>")
expect result.contains("<p>Content</p>")
```

</details>

#### builds full document

- builds full document


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds full document")
var builder = HtmlBuilder.create()
builder.add_heading(level=1, txt="Welcome")
builder.add_paragraph("Hello world")
val result = builder.build_document("My Page")
expect result.contains("<!DOCTYPE html>")
expect result.contains("<title>My Page</title>")
expect result.contains("<h1>Welcome</h1>")
```

</details>

### Common Patterns

#### creates simple page

- creates simple page


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates simple page")
val result = simple_page(title_txt="Test", heading="Welcome", content="<p>Content</p>")
expect result.contains("<title>Test</title>")
expect result.contains("<h1>Welcome</h1>")
expect result.contains("<!DOCTYPE html>")
```

</details>

#### creates page with CSS

- creates page with CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates page with CSS")
val result = page_with_css(title_txt="Styled", css_file="style.css", content="<p>Content</p>")
expect result.contains("<title>Styled</title>")
expect result.contains("rel=\"stylesheet\"")
expect result.contains("href=\"style.css\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/html_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HTML Utilities, HTML Escaping, Basic HTML Elements, Document Structure, Head Elements, Text Elements, Formatting Elements, Link Elements, Image Elements, List Elements, Table Elements, Form Elements, Semantic Elements, Builder Pattern, Common Patterns.
- HTML Utilities
- HTML Escaping
- Basic HTML Elements
- Document Structure
- Head Elements
- Text Elements
- Formatting Elements
- Link Elements
- Image Elements
- List Elements
- Table Elements
- Form Elements
- Semantic Elements
- Builder Pattern
- Common Patterns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d50d91418072b18efc2f67aa57f37eb74887ca83f54dbd90a939aec504c78405`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d50d91418072b18efc2f67aa57f37eb74887ca83f54dbd90a939aec504c78405`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d50d91418072b18efc2f67aa57f37eb74887ca83f54dbd90a939aec504c78405`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/html_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/html_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/html_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/html_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/html_utils_spec.spl:215:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes ampersand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/html_utils_spec.spl:220:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes less than' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/html_utils_spec.spl:225:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes greater than' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
