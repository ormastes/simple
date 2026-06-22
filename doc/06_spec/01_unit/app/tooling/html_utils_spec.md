# Html Utils Specification

> 1. expect escape html

<!-- sdn-diagram:id=html_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. expect escape html


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect escape_html("A & B") == "A &amp; B"
```

</details>

#### escapes less than

1. expect escape html


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect escape_html("A < B") == "A &lt; B"
```

</details>

#### escapes greater than

1. expect escape html


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect escape_html("A > B") == "A &gt; B"
```

</details>

#### escapes quotes

1. expect escape html


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect escape_html("Say \"hello\"") == "Say &quot;hello&quot;"
```

</details>

#### unescapes HTML entities

1. expect unescape html
2. expect unescape html


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect unescape_html("A &amp; B") == "A & B"
expect unescape_html("A &lt; B") == "A < B"
```

</details>

### Basic HTML Elements

#### creates simple tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tag(name="p", content="Hello")
expect result == "<p>Hello</p>"
```

</details>

#### creates self-closing tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = self_closing_tag("br")
expect result == "<br />"
```

</details>

#### creates tag with attributes

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tag_with_attrs(name="a", attrs=[("href", "/home")], content="Home")
expect result.contains("href=\"/home\"")
expect result.contains(">Home</a>")
```

</details>

### Document Structure

#### creates HTML document

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = html_document(head="<title>Test</title>", body="<p>Content</p>")
expect result.contains("<!DOCTYPE html>")
expect result.contains("<html>")
expect result.contains("<head>")
```

</details>

#### creates HTML5 document with lang

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = html5_document(lang="en", head="<title>Test</title>", body="<p>Content</p>")
expect result.contains("lang=\"en\"")
expect result.contains("<!DOCTYPE html>")
```

</details>

#### generates doctype

1. expect doctype html5


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect doctype_html5() == "<!DOCTYPE html>"
```

</details>

### Head Elements

#### creates title

1. expect title


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect title("My Page") == "<title>My Page</title>"
```

</details>

#### creates meta tag

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = meta(name="description", content="Page description")
expect result.contains("name=\"description\"")
expect result.contains("content=\"Page description\"")
```

</details>

#### creates charset meta

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = meta_charset("UTF-8")
expect result.contains("charset=\"UTF-8\"")
```

</details>

#### creates stylesheet link

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = link_stylesheet("style.css")
expect result.contains("rel=\"stylesheet\"")
expect result.contains("href=\"style.css\"")
```

</details>

### Text Elements

#### creates headings

1. expect h1
2. expect h2


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect h1("Title") == "<h1>Title</h1>"
expect h2("Subtitle") == "<h2>Subtitle</h2>"
```

</details>

#### creates paragraph

1. expect p


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect p("Paragraph") == "<p>Paragraph</p>"
```

</details>

#### creates div

1. expect div


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect div("<p>Content</p>") == "<div><p>Content</p></div>"
```

</details>

#### creates span

1. expect span


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect span("Text") == "<span>Text</span>"
```

</details>

### Formatting Elements

#### creates strong

1. expect strong


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect strong("Bold") == "<strong>Bold</strong>"
```

</details>

#### creates em

1. expect em


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect em("Italic") == "<em>Italic</em>"
```

</details>

#### creates code

1. expect code


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect code("x = 1") == "<code>x = 1</code>"
```

</details>

#### creates br

1. expect br


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect br() == "<br />"
```

</details>

#### creates hr

1. expect hr


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect hr() == "<hr />"
```

</details>

### Link Elements

#### creates anchor

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = a(href="/page", txt="Click here")
expect result.contains("href=\"/page\"")
expect result.contains(">Click here</a>")
```

</details>

#### creates external link

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = a_external(href="https://example.com", txt="Example")
expect result.contains("target=\"_blank\"")
```

</details>

### Image Elements

#### creates image

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = img(src="pic.jpg", alt="A picture")
expect result.contains("src=\"pic.jpg\"")
expect result.contains("alt=\"A picture\"")
```

</details>

### List Elements

#### creates unordered list

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ul(["Item 1", "Item 2", "Item 3"])
expect result.contains("<ul>")
expect result.contains("<li>Item 1</li>")
expect result.contains("</ul>")
```

</details>

#### creates ordered list

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ol(["First", "Second", "Third"])
expect result.contains("<ol>")
expect result.contains("<li>First</li>")
expect result.contains("</ol>")
```

</details>

#### creates list item

1. expect li


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect li("Item") == "<li>Item</li>"
```

</details>

### Table Elements

#### creates table

1. expect result contains
2. expect result contains
3. expect result contains
4. expect result contains
5. expect result contains
6. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tr(["A", "B", "C"])
expect result.contains("<tr>")
expect result.contains("<td>A</td>")
expect result.contains("</tr>")
```

</details>

#### creates th and td

1. expect th
2. expect td


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect th("Header") == "<th>Header</th>"
expect td("Data") == "<td>Data</td>"
```

</details>

### Form Elements

#### creates form

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = form(action="/submit", method="POST", content="<input>")
expect result.contains("action=\"/submit\"")
expect result.contains("method=\"POST\"")
```

</details>

#### creates text input

1. expect result contains
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = input_text(name="email", default_val="user@example.com")
expect result.contains("type=\"text\"")
expect result.contains("name=\"email\"")
```

</details>

#### creates submit button

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = button_submit("Send")
expect result.contains("type=\"submit\"")
```

</details>

### Semantic Elements

#### creates header

1. expect header


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect header("<h1>Title</h1>") == "<header><h1>Title</h1></header>"
```

</details>

#### creates footer

1. expect footer


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect footer("<p>Copyright</p>") == "<footer><p>Copyright</p></footer>"
```

</details>

#### creates nav

1. expect nav


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect nav("<ul><li>Home</li></ul>") == "<nav><ul><li>Home</li></ul></nav>"
```

</details>

#### creates main

1. expect main element


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect main_element("<p>Content</p>") == "<main><p>Content</p></main>"
```

</details>

### Builder Pattern

#### builds basic HTML

1. var builder = HtmlBuilder create
2. builder add heading
3. builder add paragraph
4. expect result contains
5. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = HtmlBuilder.create()
builder.add_heading(level=1, txt="Title")
builder.add_paragraph("Content")
val result = builder.build()
expect result.contains("<h1>Title</h1>")
expect result.contains("<p>Content</p>")
```

</details>

#### builds full document

1. var builder = HtmlBuilder create
2. builder add heading
3. builder add paragraph
4. expect result contains
5. expect result contains
6. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simple_page(title_txt="Test", heading="Welcome", content="<p>Content</p>")
expect result.contains("<title>Test</title>")
expect result.contains("<h1>Welcome</h1>")
expect result.contains("<!DOCTYPE html>")
```

</details>

#### creates page with CSS

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/tooling/html_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
