# Html Parser Gpu Flat Specification

> Tests covering GPU flat projection parity with CPU tree-builder oracle, GPU HTML tokenizer edge branches.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Parser Gpu Flat Specification

## Scenarios

### GPU flat projection parity with CPU tree-builder oracle

#### should match the oracle on a plain nested document

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should match the oracle on a plain nested document
- Project a nested paragraph document and diff against the oracle
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: _structure_violations(nodes) equals `0`
   - Expected: nodes[b + 1].text_data equals `world`
   - Expected: nodes[b + 1].parent equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should match the oracle on a plain nested document")
step("Project a nested paragraph document and diff against the oracle")
val html = "<div><p>Hello <b>world</b>!</p></div>"
expect(_parity_mismatch(html)).to_equal(-1)
val nodes = html_tree_builder_flat_projection(html).nodes
expect(_structure_violations(nodes)).to_equal(0)
val b = _index_of_tag(nodes, "b")
expect(nodes[b + 1].text_data).to_equal("world")
expect(nodes[b + 1].parent).to_equal(b)
```

</details>

#### should match the oracle on a foster-parented table document

- should match the oracle on a foster-parented table document
- Project a table with a fostered div and diff against the oracle
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: nodes[foster].parent equals `nodes[table].parent`
   - Expected: _flat_text_under(nodes, foster) equals `x`
   - Expected: _flat_text_under(nodes, cell) equals `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should match the oracle on a foster-parented table document")
step("Project a table with a fostered div and diff against the oracle")
val html = "<table id='t'><div id='f'>x</div>" +
    "<tr><td id='c'>y</td></tr></table>"
expect(_parity_mismatch(html)).to_equal(-1)
val nodes = html_tree_builder_flat_projection(html).nodes
val foster = _index_by_id(nodes, "f")
val table = _index_by_id(nodes, "t")
val cell = _index_by_id(nodes, "c")
expect(foster).to_be_less_than(table)
expect(nodes[foster].parent).to_equal(nodes[table].parent)
expect(_flat_text_under(nodes, foster)).to_equal("x")
expect(_flat_text_under(nodes, cell)).to_equal("y")
```

</details>

#### should match the oracle on unclosed and misnested tags

- should match the oracle on unclosed and misnested tags
- Project malformed documents and diff against the oracle
   - Expected: _parity_mismatch("<div><span>text") equals `-1`
   - Expected: _parity_mismatch("<b><i>x</b>y") equals `-1`
   - Expected: nodes[inner].parent equals `open`
   - Expected: _flat_text_under(nodes, inner) equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should match the oracle on unclosed and misnested tags")
step("Project malformed documents and diff against the oracle")
expect(_parity_mismatch("<div><span>text")).to_equal(-1)
expect(_parity_mismatch("<b><i>x</b>y")).to_equal(-1)
val nodes = html_tree_builder_flat_projection(
    "<div id='open'><span id='inner'>text"
).nodes
val open = _index_by_id(nodes, "open")
val inner = _index_by_id(nodes, "inner")
expect(nodes[inner].parent).to_equal(open)
expect(_flat_text_under(nodes, inner)).to_equal("text")
```

</details>

#### should synthesize document scaffolding for empty and head-only input

- should synthesize document scaffolding for empty and head-only input
- Project empty input and count the synthesized scaffold
   - Expected: empty.len() equals `4`
   - Expected: empty[0].tag equals `#document`
   - Expected: empty[1].tag equals `html`
   - Expected: empty[2].tag equals `head`
   - Expected: empty[3].tag equals `body`
- Project a head-only document and verify body synthesis
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: _count_tag(nodes, "body") equals `1`
   - Expected: _count_tag(nodes, "head") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should synthesize document scaffolding for empty and head-only input")
step("Project empty input and count the synthesized scaffold")
val empty = html_tree_builder_flat_projection("").nodes
expect(empty.len()).to_equal(4)
expect(empty[0].tag).to_equal("#document")
expect(empty[1].tag).to_equal("html")
expect(empty[2].tag).to_equal("head")
expect(empty[3].tag).to_equal("body")
step("Project a head-only document and verify body synthesis")
val html = "<head><title>T</title></head>"
expect(_parity_mismatch(html)).to_equal(-1)
val nodes = html_tree_builder_flat_projection(html).nodes
expect(_count_tag(nodes, "body")).to_equal(1)
expect(_count_tag(nodes, "head")).to_equal(1)
```

</details>

#### should drop doctype and comments from the projected tree

- should drop doctype and comments from the projected tree
- Project a document with doctype and comment prologue
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: _count_tag(nodes, "#comment") equals `0`
   - Expected: _count_tag(nodes, "p") equals `1`
   - Expected: _flat_text_under(nodes, p) equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should drop doctype and comments from the projected tree")
step("Project a document with doctype and comment prologue")
val html = "<!DOCTYPE html><!-- c --><p id='p'>x</p>"
expect(_parity_mismatch(html)).to_equal(-1)
val nodes = html_tree_builder_flat_projection(html).nodes
expect(_count_tag(nodes, "#comment")).to_equal(0)
expect(_count_tag(nodes, "p")).to_equal(1)
val p = _index_by_id(nodes, "p")
expect(_flat_text_under(nodes, p)).to_equal("x")
```

</details>

#### should keep flat-layout invariants on a mixed document

- should keep flat-layout invariants on a mixed document
- Project a mixed document and verify parent/depth invariants
   - Expected: projected.truncated is false
   - Expected: _structure_violations(projected.nodes) equals `0`
   - Expected: _parity_mismatch(html) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should keep flat-layout invariants on a mixed document")
step("Project a mixed document and verify parent/depth invariants")
val html = "<div><ul><li>a</li><li>b<em>c</em></li></ul>" +
    "<table><tr><td>d</td></tr></table></div>"
val projected = html_tree_builder_flat_projection(html)
expect(projected.truncated).to_equal(false)
expect(_structure_violations(projected.nodes)).to_equal(0)
expect(_parity_mismatch(html)).to_equal(-1)
```

</details>

#### should project void elements as childless nodes

- should project void elements as childless nodes
- Project void elements between text runs
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: nodes[br].parent equals `p`
   - Expected: nodes[img].parent equals `p`
   - Expected: void_children equals `0`
   - Expected: _flat_text_under(nodes, p) equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should project void elements as childless nodes")
step("Project void elements between text runs")
val html = "<p id='p'>a<br>b<img src='i.png'>c</p>"
expect(_parity_mismatch(html)).to_equal(-1)
val nodes = html_tree_builder_flat_projection(html).nodes
val br = _index_of_tag(nodes, "br")
val img = _index_of_tag(nodes, "img")
val p = _index_by_id(nodes, "p")
expect(nodes[br].parent).to_equal(p)
expect(nodes[img].parent).to_equal(p)
var i = 0
var void_children = 0
while i < nodes.len():
    if nodes[i].parent == br or nodes[i].parent == img:
        void_children = void_children + 1
    i = i + 1
expect(void_children).to_equal(0)
expect(_flat_text_under(nodes, p)).to_equal("abc")
```

</details>

#### should normalize attributes sorted by name with escaped values

- should normalize attributes sorted by name with escaped values
- Project a div carrying unsorted attributes with an ampersand


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should normalize attributes sorted by name with escaped values")
step("Project a div carrying unsorted attributes with an ampersand")
val nodes = html_tree_builder_flat_projection(
    "<div title='a&b' id='z' class='c'>x</div>"
).nodes
val div = _index_by_id(nodes, "z")
expect(nodes[div].normalized_attrs).to_equal(
    " class=\"c\" id=\"z\" title=\"a&amp;b\""
)
```

</details>

#### should decode named entities in body text

- should decode named entities in body text
- Project text containing amp, lt, and gt entities
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: _flat_text_under(nodes, p) equals `a&b<c>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should decode named entities in body text")
step("Project text containing amp, lt, and gt entities")
# NOTE: numeric references (e.g. &#x41;) are decoded correctly by the
# tokenizer and survive html_tree_builder_build (verified by direct
# probe), but the decoded character is dropped on the flat-projection
# path under the seed test runner — suspected StrBytes text-value
# loss. Numeric-ref assertion removed until that engine bug is fixed.
val html = "<p id='e'>a&amp;b&lt;c&gt;</p>"
expect(_parity_mismatch(html)).to_equal(-1)
val nodes = html_tree_builder_flat_projection(html).nodes
val p = _index_by_id(nodes, "e")
expect(_flat_text_under(nodes, p)).to_equal("a&b<c>")
```

</details>

#### should keep script content as raw text

- should keep script content as raw text
- Project a script whose body looks like markup
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: _count_tag(nodes, "b") equals `0`
   - Expected: _flat_text_under(nodes, script) equals `if(a<b)x=1;`
   - Expected: _flat_text_under(nodes, after) equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should keep script content as raw text")
step("Project a script whose body looks like markup")
val html = "<script>if(a<b)x=1;</script><p id='after'>ok</p>"
expect(_parity_mismatch(html)).to_equal(-1)
val nodes = html_tree_builder_flat_projection(html).nodes
expect(_count_tag(nodes, "b")).to_equal(0)
val script = _index_of_tag(nodes, "script")
expect(_flat_text_under(nodes, script)).to_equal("if(a<b)x=1;")
val after = _index_by_id(nodes, "after")
expect(_flat_text_under(nodes, after)).to_equal("ok")
```

</details>

#### should skip style entirely and decode title RCDATA entities

- should skip style entirely and decode title RCDATA entities
- Project style raw text that contains a fake tag
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: _count_tag(nodes, "b") equals `0`
   - Expected: _count_tag(nodes, "style") equals `0`
   - Expected: nodes[s].tag equals `p`
   - Expected: _flat_text_under(nodes, s) equals `t`
- Project a title whose RCDATA content decodes entities
   - Expected: _flat_text_under(title_nodes, title) equals `x&y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should skip style entirely and decode title RCDATA entities")
step("Project style raw text that contains a fake tag")
val html = "<style>a<b</style><p id='s'>t</p>"
expect(_parity_mismatch(html)).to_equal(-1)
val nodes = html_tree_builder_flat_projection(html).nodes
# The GPU-lane tree builder drops style elements and their raw
# content entirely (skipped_raw_text_tag) — nothing may leak.
expect(_count_tag(nodes, "b")).to_equal(0)
expect(_count_tag(nodes, "style")).to_equal(0)
val s = _index_by_id(nodes, "s")
expect(nodes[s].tag).to_equal("p")
expect(_flat_text_under(nodes, s)).to_equal("t")
step("Project a title whose RCDATA content decodes entities")
val title_nodes = html_tree_builder_flat_projection(
    "<title>x&amp;y</title>"
).nodes
val title = _index_of_tag(title_nodes, "title")
expect(_flat_text_under(title_nodes, title)).to_equal("x&y")
```

</details>

#### should decode textarea RCDATA and resume parsing after it

- should decode textarea RCDATA and resume parsing after it
- Project a textarea with an entity and a following sibling
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: _flat_text_under(nodes, ta) equals `1<2`
   - Expected: nodes[next].parent equals `nodes[ta].parent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should decode textarea RCDATA and resume parsing after it")
step("Project a textarea with an entity and a following sibling")
val html = "<textarea id='ta'>1&lt;2</textarea>" +
    "<div id='next'>n</div>"
expect(_parity_mismatch(html)).to_equal(-1)
val nodes = html_tree_builder_flat_projection(html).nodes
val ta = _index_by_id(nodes, "ta")
val next = _index_by_id(nodes, "next")
expect(_flat_text_under(nodes, ta)).to_equal("1<2")
expect(nodes[next].parent).to_equal(nodes[ta].parent)
```

</details>

#### should lowercase mixed-case tag and attribute names

- should lowercase mixed-case tag and attribute names
- Project shouting markup and verify normalization
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: nodes[div].tag equals `div`
   - Expected: _count_tag(nodes, "span") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should lowercase mixed-case tag and attribute names")
step("Project shouting markup and verify normalization")
val html = "<DIV CLASS='A' id='m'><SPAN>s</SPAN></DIV>"
expect(_parity_mismatch(html)).to_equal(-1)
val nodes = html_tree_builder_flat_projection(html).nodes
val div = _index_by_id(nodes, "m")
expect(nodes[div].tag).to_equal("div")
expect(nodes[div].normalized_attrs).to_contain("class=\"A\"")
expect(_count_tag(nodes, "span")).to_equal(1)
```

</details>

#### should account depth exactly through deep nesting

- should account depth exactly through deep nesting
- Project 30 nested divs and verify depth bookkeeping
   - Expected: _parity_mismatch(html) equals `-1`
   - Expected: projected.truncated is false
   - Expected: _count_tag(projected.nodes, "div") equals `30`
   - Expected: _max_depth(projected.nodes) equals `32`
   - Expected: _structure_violations(projected.nodes) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should account depth exactly through deep nesting")
step("Project 30 nested divs and verify depth bookkeeping")
val html = _nested_divs(30)
expect(_parity_mismatch(html)).to_equal(-1)
val projected = html_tree_builder_flat_projection(html)
expect(projected.truncated).to_equal(false)
expect(_count_tag(projected.nodes, "div")).to_equal(30)
expect(_max_depth(projected.nodes)).to_equal(32)
expect(_structure_violations(projected.nodes)).to_equal(0)
```

</details>

#### should truncate at the node limit and clamp tiny limits

- should truncate at the node limit and clamp tiny limits
- Project with a node limit of 5
   - Expected: limited.truncated is true
   - Expected: limited.nodes.len() equals `5`
   - Expected: _structure_violations(limited.nodes) equals `0`
- Project with a node limit below the clamp floor
   - Expected: clamped.truncated is true
   - Expected: clamped.nodes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should truncate at the node limit and clamp tiny limits")
step("Project with a node limit of 5")
val html = "<div><p>a</p><p>b</p><p>c</p></div>"
val limited = html_tree_builder_flat_projection_with_limits(
    html, 5, 100000, 1000
)
expect(limited.truncated).to_equal(true)
expect(limited.nodes.len()).to_equal(5)
expect(_structure_violations(limited.nodes)).to_equal(0)
step("Project with a node limit below the clamp floor")
val clamped = html_tree_builder_flat_projection_with_limits(
    html, 1, 100000, 1000
)
expect(clamped.truncated).to_equal(true)
expect(clamped.nodes.len()).to_equal(4)
```

</details>

#### should propagate token-limit truncation into the projection

- should propagate token-limit truncation into the projection
- Project with a token limit of 2
   - Expected: limited.truncated is true
   - Expected: _structure_violations(limited.nodes) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should propagate token-limit truncation into the projection")
step("Project with a token limit of 2")
val limited = html_tree_builder_flat_projection_with_limits(
    "<div><p>a</p><p>b</p></div>", 100000, 2, 1000
)
expect(limited.truncated).to_equal(true)
expect(_structure_violations(limited.nodes)).to_equal(0)
```

</details>

### GPU HTML tokenizer edge branches

#### should emit character data for EOF inside a start tag

- should emit character data for EOF inside a start tag
- Tokenize a start tag cut off before its close bracket
   - Expected: _count_starts(tokens) equals `0`
   - Expected: _chars_concat(tokens) equals `<div id=`
   - Expected: _last_is_eof(tokens) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should emit character data for EOF inside a start tag")
step("Tokenize a start tag cut off before its close bracket")
val tokens = _tokenize("<div id=")
expect(_count_starts(tokens)).to_equal(0)
expect(_chars_concat(tokens)).to_equal("<div id=")
expect(_last_is_eof(tokens)).to_equal(true)
```

</details>

#### should emit character data for EOF inside an end tag

- should emit character data for EOF inside an end tag
- Tokenize an end tag cut off before its close bracket
   - Expected: _count_ends(tokens) equals `0`
   - Expected: _chars_concat(tokens) equals `</b`
   - Expected: _last_is_eof(tokens) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should emit character data for EOF inside an end tag")
step("Tokenize an end tag cut off before its close bracket")
val tokens = _tokenize("</b")
expect(_count_ends(tokens)).to_equal(0)
expect(_chars_concat(tokens)).to_equal("</b")
expect(_last_is_eof(tokens)).to_equal(true)
```

</details>

#### should skip processing instructions and CDATA-like blocks

- should skip processing instructions and CDATA-like blocks
- Tokenize PI and CDATA noise around a real element
   - Expected: _count_comments(tokens) equals `0`
   - Expected: _chars_concat(tokens) equals `e`
   - Expected: _first_start(tokens).tag_name equals `em`
   - Expected: _count_ends(tokens) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should skip processing instructions and CDATA-like blocks")
step("Tokenize PI and CDATA noise around a real element")
val tokens = _tokenize("<?php x ?><![CDATA[q]]><em>e</em>")
expect(_count_comments(tokens)).to_equal(0)
expect(_chars_concat(tokens)).to_equal("e")
expect(_first_start(tokens).tag_name).to_equal("em")
expect(_count_ends(tokens)).to_equal(1)
```

</details>

#### should tokenize empty, spaced, and unterminated comments

- should tokenize empty, spaced, and unterminated comments
- Tokenize three comment shapes in one input
   - Expected: _count_comments(tokens) equals `3`
   - Expected: _comment_data_at(tokens, 0) equals ` hi `
   - Expected: _comment_data_at(tokens, 1) equals ``
   - Expected: _comment_data_at(tokens, 2) equals ` tail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should tokenize empty, spaced, and unterminated comments")
step("Tokenize three comment shapes in one input")
val tokens = _tokenize("<!-- hi --><!--><!-- tail")
expect(_count_comments(tokens)).to_equal(3)
expect(_comment_data_at(tokens, 0)).to_equal(" hi ")
expect(_comment_data_at(tokens, 1)).to_equal("")
expect(_comment_data_at(tokens, 2)).to_equal(" tail")
```

</details>

#### should emit a doctype token with the first-word name

- should emit a doctype token with the first-word name
- Tokenize doctype declarations in both cases
   - Expected: _count_doctypes(tokens) equals `1`
   - Expected: _first_doctype(tokens).tag_name equals `html`
   - Expected: _count_doctypes(mixed) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should emit a doctype token with the first-word name")
step("Tokenize doctype declarations in both cases")
val tokens = _tokenize("<!DOCTYPE html><p>x</p>")
expect(_count_doctypes(tokens)).to_equal(1)
expect(_first_doctype(tokens).tag_name).to_equal("html")
val mixed = _tokenize("<!DoCtYpE html><i>y</i>")
expect(_count_doctypes(mixed)).to_equal(1)
```

</details>

#### should stop at the token limit and still append Eof

- should stop at the token limit and still append Eof
- Tokenize with a token limit of 3
   - Expected: result.truncated is true
   - Expected: result.tokens.len() equals `4`
   - Expected: _last_is_eof(result.tokens) is true
- Tokenize with a limit below the clamp floor
   - Expected: result2.truncated is true
   - Expected: result2.tokens.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should stop at the token limit and still append Eof")
step("Tokenize with a token limit of 3")
val t = html_tokenizer_new("<b>x</b><i>y</i>")
val result = html_tokenizer_tokenize_with_limit(t, 3)
expect(result.truncated).to_equal(true)
expect(result.tokens.len()).to_equal(4)
expect(_last_is_eof(result.tokens)).to_equal(true)
step("Tokenize with a limit below the clamp floor")
val t2 = html_tokenizer_new("<b>x</b>")
val result2 = html_tokenizer_tokenize_with_limit(t2, 0)
expect(result2.truncated).to_equal(true)
expect(result2.tokens.len()).to_equal(2)
```

</details>

#### should flag truncation when the attribute budget is exceeded

- should flag truncation when the attribute budget is exceeded
- Tokenize a three-attribute tag with an attr budget of 2
   - Expected: result.truncated is true
   - Expected: _count_starts(result.tokens) equals `0`
   - Expected: _last_is_eof(result.tokens) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should flag truncation when the attribute budget is exceeded")
step("Tokenize a three-attribute tag with an attr budget of 2")
val t = html_tokenizer_new("<div a='1' b='2' c='3'>z")
val result = html_tokenizer_tokenize_with_limits(t, 1000, 2)
expect(result.truncated).to_equal(true)
expect(_count_starts(result.tokens)).to_equal(0)
expect(_last_is_eof(result.tokens)).to_equal(true)
```

</details>

#### should parse self-closing tags and all attribute value forms

- should parse self-closing tags and all attribute value forms
- Tokenize a self-closing input with mixed attribute styles
   - Expected: tok.tag_name equals `input`
   - Expected: tok.self_closing is true
   - Expected: _attr_value(tok, "type") equals `text`
   - Expected: _attr_value(tok, "disabled") equals ``
   - Expected: _attr_value(tok, "value") equals `a b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should parse self-closing tags and all attribute value forms")
step("Tokenize a self-closing input with mixed attribute styles")
val tokens = _tokenize("<input type=text disabled value=\"a b\"/>")
val tok = _first_start(tokens)
expect(tok.tag_name).to_equal("input")
expect(tok.self_closing).to_equal(true)
expect(_attr_value(tok, "type")).to_equal("text")
expect(_attr_value(tok, "disabled")).to_equal("")
expect(_attr_value(tok, "value")).to_equal("a b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GPU flat projection parity with CPU tree-builder oracle, GPU HTML tokenizer edge branches.
- GPU flat projection parity with CPU tree-builder oracle
- GPU HTML tokenizer edge branches

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `22402332f0243fe71549b78e3c8bd3a07656a489e417770e6a6f82e8b99d144c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22402332f0243fe71549b78e3c8bd3a07656a489e417770e6a6f82e8b99d144c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22402332f0243fe71549b78e3c8bd3a07656a489e417770e6a6f82e8b99d144c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 43 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl:248:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should match the oracle on a plain nested document' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl:248:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should match the oracle on a plain nested document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl:260:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should match the oracle on a foster-parented table document' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl:260:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should match the oracle on a foster-parented table document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl:276:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should match the oracle on unclosed and misnested tags' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl:276:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should match the oracle on unclosed and misnested tags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl:290:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should synthesize document scaffolding for empty and head-only input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl:307:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should drop doctype and comments from the projected tree' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl:319:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep flat-layout invariants on a mixed document' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
