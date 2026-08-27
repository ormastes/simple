# Css Parser Gpu Tables Specification

> Tests covering css parser gpu tables — style block parsing, css parser gpu tables — selector matcher, css parser gpu tables — rule index tables, css parser gpu tables — resolver selector matching, css parser gpu tables — cpu parity direct vs indexed lane, css parser gpu tables — shorthand declaration expansion, css parser gpu tables — :has() relational matching, css parser gpu tables — attribute and positional selector edges.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 62 | 62 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Css Parser Gpu Tables Specification

## Scenarios

### css parser gpu tables — style block parsing

#### extracts multiple style blocks from html

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts multiple style blocks from html
   - Expected: blocks.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts multiple style blocks from html")
val html = "<html><head><style>p { color: red; }</style>" +
    "<style type=\"text/css\">.a { margin-top: 1px; }</style></head></html>"
val blocks = extract_style_blocks(html)
expect(blocks.len()).to_equal(2)
expect(blocks[0].contains("color: red")).to_be_true()
expect(blocks[1].contains("margin-top: 1px")).to_be_true()
```

</details>

#### returns no blocks when html has no style element

- returns no blocks when html has no style element
   - Expected: blocks.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns no blocks when html has no style element")
val blocks = extract_style_blocks("<html><body><p>hi</p></body></html>")
expect(blocks.len()).to_equal(0)
```

</details>

#### parses a simple rule into selector and declarations

- parses a simple rule into selector and declarations
   - Expected: rules.len() equals `1`
   - Expected: rules[0].selector equals `h1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a simple rule into selector and declarations")
val rules = parse_css_rules("h1 { color: blue; font-size: 20px; }")
expect(rules.len()).to_equal(1)
expect(rules[0].selector).to_equal("h1")
expect(css_decls_contain(rules[0].declarations, "color", "blue")).to_be_true()
expect(css_decls_contain(rules[0].declarations, "font-size", "20px")).to_be_true()
```

</details>

#### splits a selector list into one rule per selector

- splits a selector list into one rule per selector
   - Expected: rules.len() equals `2`
   - Expected: rules[0].selector equals `h1`
   - Expected: rules[1].selector equals `h2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("splits a selector list into one rule per selector")
val rules = parse_css_rules("h1, h2 { color: green; }")
expect(rules.len()).to_equal(2)
expect(rules[0].selector).to_equal("h1")
expect(rules[1].selector).to_equal("h2")
expect(css_decls_contain(rules[1].declarations, "color", "green")).to_be_true()
```

</details>

#### skips comments between rules

- skips comments between rules
   - Expected: rules.len() equals `2`
   - Expected: rules[0].selector equals `p`
   - Expected: rules[1].selector equals `span`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips comments between rules")
val rules = parse_css_rules("/* lead comment */ p { color: red; } /* tail */ span { color: blue; }")
expect(rules.len()).to_equal(2)
expect(rules[0].selector).to_equal("p")
expect(rules[1].selector).to_equal("span")
```

</details>

#### recovers from a truncated rule without crashing

- recovers from a truncated rule without crashing
   - Expected: rules.len() equals `1`
   - Expected: rules[0].selector equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("recovers from a truncated rule without crashing")
val rules = parse_css_rules("p { color: red; } div { margin-top: 1px")
expect(rules.len()).to_equal(1)
expect(rules[0].selector).to_equal("p")
```

</details>

#### parses declarations skipping malformed segments

- parses declarations skipping malformed segments
   - Expected: decls.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses declarations skipping malformed segments")
val decls = parse_declarations("color: red;; not-a-decl ; width: 10px;")
expect(decls.len()).to_equal(2)
expect(css_decls_contain(decls, "color", "red")).to_be_true()
expect(css_decls_contain(decls, "width", "10px")).to_be_true()
```

</details>

#### keeps !important in the declaration value

- keeps !important in the declaration value
   - Expected: decls.len() equals `1`
   - Expected: decls[0].property equals `color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps !important in the declaration value")
val decls = parse_declarations("color: red !important")
expect(decls.len()).to_equal(1)
expect(decls[0].property).to_equal("color")
expect(decls[0].value.contains("!important")).to_be_true()
expect(decls[0].value.contains("red")).to_be_true()
```

</details>

#### expands margin box shorthand to four sides

- expands margin box shorthand to four sides
   - Expected: decls.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands margin box shorthand to four sides")
val decls = parse_declarations("margin: 1px 2px 3px 4px")
expect(decls.len()).to_equal(4)
expect(css_decls_contain(decls, "margin-top", "1px")).to_be_true()
expect(css_decls_contain(decls, "margin-right", "2px")).to_be_true()
expect(css_decls_contain(decls, "margin-bottom", "3px")).to_be_true()
expect(css_decls_contain(decls, "margin-left", "4px")).to_be_true()
```

</details>

#### expands flex-flow into direction and wrap

- expands flex-flow into direction and wrap
   - Expected: decls.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands flex-flow into direction and wrap")
val decls = expand_flex_flow("column wrap")
expect(decls.len()).to_equal(2)
expect(css_decls_contain(decls, "flex-direction", "column")).to_be_true()
expect(css_decls_contain(decls, "flex-wrap", "wrap")).to_be_true()
```

</details>

#### collects custom properties from :root and resolves var() references

- collects custom properties from :root and resolves var() references
   - Expected: vars.len() equals `1`
   - Expected: vars[0].property equals `--main-color`
   - Expected: vars[0].value equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects custom properties from :root and resolves var() references")
val css = ":root { --main-color: red; } p { color: var(--main-color); }"
val rules = parse_css_rules(css)
val vars = collect_css_vars(rules)
expect(vars.len()).to_equal(1)
expect(vars[0].property).to_equal("--main-color")
expect(vars[0].value).to_equal("red")
val resolved = resolve_css_vars_in_rules(rules, vars)
var found = false
var i = 0
while i < resolved.len():
    val rule = resolved[i]
    i = i + 1
    if rule.selector == "p":
        found = css_decls_contain(rule.declarations, "color", "red")
expect(found).to_be_true()
```

</details>

#### extracts keyframes with normalized offsets

- extracts keyframes with normalized offsets
   - Expected: registry.entries.len() equals `1`
   - Expected: registry.entries[0].name equals `fade`
   - Expected: frames.len() equals `3`
   - Expected: frames[0].offset equals `0.0`
   - Expected: frames[1].offset equals `0.5`
   - Expected: frames[2].offset equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts keyframes with normalized offsets")
val css = "@keyframes fade { from { opacity: 0; } 50% { opacity: 0.5; } to { opacity: 1; } }"
val registry = extract_keyframes(css)
expect(registry.entries.len()).to_equal(1)
expect(registry.entries[0].name).to_equal("fade")
val frames = registry.entries[0].frames
expect(frames.len()).to_equal(3)
expect(frames[0].offset).to_equal(0.0)
expect(frames[1].offset).to_equal(0.5)
expect(frames[2].offset).to_equal(1.0)
```

</details>

#### strips @keyframes bodies from the flat rule table

- strips @keyframes bodies from the flat rule table
   - Expected: rules.len() equals `1`
   - Expected: rules[0].selector equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("strips @keyframes bodies from the flat rule table")
val css = "@keyframes slide { from { left: 0px; } to { left: 10px; } } p { color: red; }"
val rules = parse_css_rules(css)
expect(rules.len()).to_equal(1)
expect(rules[0].selector).to_equal("p")
```

</details>

#### surfaces rules inside @supports and @layer blocks

- surfaces rules inside @supports and @layer blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("surfaces rules inside @supports and @layer blocks")
val css = "@supports (display: flex) { .s { color: red; } } @layer base { .l { color: blue; } }"
val rules = parse_css_rules(css)
var s_found = false
var l_found = false
var i = 0
while i < rules.len():
    val rule = rules[i]
    i = i + 1
    if rule.selector == ".s":
        s_found = css_decls_contain(rule.declarations, "color", "red")
    if rule.selector == ".l":
        l_found = css_decls_contain(rule.declarations, "color", "blue")
expect(s_found).to_be_true()
expect(l_found).to_be_true()
```

</details>

#### flattens parent-referencing nested rules

- flattens parent-referencing nested rules


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flattens parent-referencing nested rules")
val css = ".card { color: red; & .inner { color: blue; } }"
val rules = parse_css_rules(css)
var nested_found = false
var i = 0
while i < rules.len():
    val rule = rules[i]
    i = i + 1
    if rule.selector == ".card .inner":
        nested_found = css_decls_contain(rule.declarations, "color", "blue")
expect(nested_found).to_be_true()
```

</details>

### css parser gpu tables — selector matcher

#### extracts the tag name from bracketed tag content

- extracts the tag name from bracketed tag content
   - Expected: br_tag_name_from_content("<div class=\"x\" id=\"y\">") equals `div`
   - Expected: br_tag_name_from_content("<SPAN>") equals `span`
   - Expected: br_tag_name_from_content("no brackets") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts the tag name from bracketed tag content")
expect(br_tag_name_from_content("<div class=\"x\" id=\"y\">")).to_equal("div")
expect(br_tag_name_from_content("<SPAN>")).to_equal("span")
expect(br_tag_name_from_content("no brackets")).to_equal("")
```

</details>

#### matches :not against attribute substring options

- matches :not against attribute substring options


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches :not against attribute substring options")
val tag = "a href=\"https://example.test/docs\" class=\"nav\""
expect(br_selector_list_contains_not_self("a:not([href*=\"admin\"])", "a", tag)).to_be_true()
val admin_tag = "a href=\"https://example.test/admin\" class=\"nav\""
expect(br_selector_list_contains_not_self("a:not([href*=\"admin\"])", "a", admin_tag)).to_be_false()
```

</details>

#### matches attribute-self substring options against tag content

- matches attribute-self substring options against tag content


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches attribute-self substring options against tag content")
# Only the [attr*="value"] substring operator is supported by the
# option matcher; exact [attr="value"] is not implemented there.
val tag = "input type=\"text\" name=\"q\""
expect(br_selector_list_contains_attr_self("input[type*=\"tex\"]", "input", tag)).to_be_true()
expect(br_selector_list_contains_attr_self("input[type*=\"radio\"]", "input", tag)).to_be_false()
```

</details>

#### matches compound tag.class options against tag content

- matches compound tag.class options against tag content


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches compound tag.class options against tag content")
val tag = "button class=\"primary big\""
expect(br_selector_list_contains_attr_self("button.primary", "button", tag)).to_be_true()
expect(br_selector_list_contains_attr_self("button.ghost", "button", tag)).to_be_false()
expect(br_selector_list_contains_attr_self("a.primary", "button", tag)).to_be_false()
```

</details>

#### requires every class for multi-class selectors

- requires every class for multi-class selectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires every class for multi-class selectors")
expect(br_selector_list_contains_multi_class(".a.b { }", ["a", "b"])).to_be_true()
expect(br_selector_list_contains_multi_class(".a { }", ["a", "b"])).to_be_false()
```

</details>

### css parser gpu tables — rule index tables

#### returns empty for a blank selector or missing style block

- returns empty for a blank selector or missing style block
   - Expected: br_style_block_rule_for_selector("<html></html>", ".x") equals ``
   - Expected: br_style_block_rule_for_selector("<html><style>.x { color: red; }</style></html>", "") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty for a blank selector or missing style block")
expect(br_style_block_rule_for_selector("<html></html>", ".x")).to_equal("")
expect(br_style_block_rule_for_selector("<html><style>.x { color: red; }</style></html>", "")).to_equal("")
```

</details>

#### returns empty for blank class, id and combinator arguments

- returns empty for blank class, id and combinator arguments
   - Expected: br_style_block_rule_for_class(html, "") equals ``
   - Expected: br_style_block_rule_for_id(html, "  ") equals ``
   - Expected: br_style_block_rule_for_tag_class(html, "div", "") equals ``
   - Expected: br_style_block_rule_for_tag_id(html, "div", "") equals ``
   - Expected: br_style_block_rule_for_descendant(html, "", "span") equals ``
   - Expected: br_style_block_rule_for_child(html, "ul", " ") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty for blank class, id and combinator arguments")
val html = "<html><head><style>.a { color: red; }</style></head><body></body></html>"
expect(br_style_block_rule_for_class(html, "")).to_equal("")
expect(br_style_block_rule_for_id(html, "  ")).to_equal("")
expect(br_style_block_rule_for_tag_class(html, "div", "")).to_equal("")
expect(br_style_block_rule_for_tag_id(html, "div", "")).to_equal("")
expect(br_style_block_rule_for_descendant(html, "", "span")).to_equal("")
expect(br_style_block_rule_for_child(html, "ul", " ")).to_equal("")
```

</details>

#### returns empty from selector lookups when the document has no style block

- returns empty from selector lookups when the document has no style block
   - Expected: br_style_block_rule_for_class(bare, "a") equals ``
   - Expected: br_style_block_rule_for_id(bare, "main") equals ``
   - Expected: br_style_block_rule_for_tag(bare, "div") equals ``
   - Expected: br_style_block_rule_for_universal(bare) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty from selector lookups when the document has no style block")
val bare = "<html><body><div class=\"a\"></div></body></html>"
expect(br_style_block_rule_for_class(bare, "a")).to_equal("")
expect(br_style_block_rule_for_id(bare, "main")).to_equal("")
expect(br_style_block_rule_for_tag(bare, "div")).to_equal("")
expect(br_style_block_rule_for_universal(bare)).to_equal("")
```

</details>

#### matches multi-class table entries only when all classes present

- matches multi-class table entries only when all classes present
   - Expected: br_style_block_rule_for_multi_class(html, "a ghost") equals ``
   - Expected: br_style_block_rule_for_multi_class(html, "a") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches multi-class table entries only when all classes present")
val html = "<html><head><style>.a.b { color: red; }</style></head><body></body></html>"
expect(br_style_block_rule_for_multi_class(html, "a b").contains("color: red")).to_be_true()
expect(br_style_block_rule_for_multi_class(html, "a ghost")).to_equal("")
# fewer than two classes never consults the multi-class table
expect(br_style_block_rule_for_multi_class(html, "a")).to_equal("")
```

</details>

#### merges multi-class rules found across multiple style blocks

- merges multi-class rules found across multiple style blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merges multi-class rules found across multiple style blocks")
val html = "<html><head><style>.a.b { color: red; }</style>" +
    "<style>.a.b { width: 7px; }</style></head><body></body></html>"
val out = br_style_block_rule_for_multi_class(html, "a b")
expect(out.contains("color: red")).to_be_true()
expect(out.contains("width: 7px")).to_be_true()
```

</details>

#### for_selector returns declarations from a non-empty style block

- for_selector returns declarations from a non-empty style block
   - Expected: br_style_block_rule_for_selector(html, ".zz") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("for_selector returns declarations from a non-empty style block")
val html = "<html><head><style>.x { color: red; } .y { width: 4px; }</style></head><body></body></html>"
expect(br_style_block_rule_for_selector(html, ".x").contains("color: red")).to_be_true()
expect(br_style_block_rule_for_selector(html, ".x").contains("width: 4px")).to_be_false()
expect(br_style_block_rule_for_selector(html, ".zz")).to_equal("")
```

</details>

#### merges for_selector declarations across multiple style blocks

- merges for_selector declarations across multiple style blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merges for_selector declarations across multiple style blocks")
val html = "<html><head><style>.x { color: red; }</style>" +
    "<style>.x { width: 7px; }</style></head><body></body></html>"
val out = br_style_block_rule_for_selector(html, ".x")
expect(out.contains("color: red")).to_be_true()
expect(out.contains("width: 7px")).to_be_true()
```

</details>

#### class and id table lookups surface rules from a non-empty style block

- class and id table lookups surface rules from a non-empty style block
   - Expected: br_style_block_rule_for_class(html, "ghost") equals ``
   - Expected: br_style_block_rule_for_id(html, "other") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("class and id table lookups surface rules from a non-empty style block")
val html = "<html><head><style>.btn { color: red; } #main { width: 100px; }</style></head><body></body></html>"
expect(br_style_block_rule_for_class(html, "btn").contains("color: red")).to_be_true()
expect(br_style_block_rule_for_class(html, "ghost")).to_equal("")
expect(br_style_block_rule_for_id(html, "main").contains("width: 100px")).to_be_true()
expect(br_style_block_rule_for_id(html, "other")).to_equal("")
```

</details>

#### tag and universal table lookups surface rules from a non-empty style block

- tag and universal table lookups surface rules from a non-empty style block
   - Expected: br_style_block_rule_for_tag(html, "em") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tag and universal table lookups surface rules from a non-empty style block")
val html = "<html><head><style>div { margin-top: 3px; } * { box-sizing: border-box; }</style></head><body></body></html>"
expect(br_style_block_rule_for_tag(html, "div").contains("margin-top: 3px")).to_be_true()
expect(br_style_block_rule_for_tag(html, "em")).to_equal("")
expect(br_style_block_rule_for_universal(html).contains("box-sizing: border-box")).to_be_true()
```

</details>

#### tag.class and tag#id compound lookups surface their rules

- tag.class and tag#id compound lookups surface their rules
   - Expected: br_style_block_rule_for_tag_class(html, "em", "btn") equals ``
   - Expected: br_style_block_rule_for_tag_id(html, "div", "other") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tag.class and tag#id compound lookups surface their rules")
val html = "<html><head><style>div.btn { color: navy; } div#main { width: 7px; } span.btn { color: olive; }</style></head><body></body></html>"
val tc = br_style_block_rule_for_tag_class(html, "div", "btn")
expect(tc.contains("color: navy")).to_be_true()
expect(tc.contains("color: olive")).to_be_false()
expect(br_style_block_rule_for_tag_class(html, "em", "btn")).to_equal("")
expect(br_style_block_rule_for_tag_id(html, "div", "main").contains("width: 7px")).to_be_true()
expect(br_style_block_rule_for_tag_id(html, "div", "other")).to_equal("")
```

</details>

#### descendant and child combinator lookups surface their rules

- descendant and child combinator lookups surface their rules
   - Expected: br_style_block_rule_for_descendant(html, "nav", "li") equals ``
   - Expected: br_style_block_rule_for_child(html, "ol", "li") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("descendant and child combinator lookups surface their rules")
val html = "<html><head><style>ul li { color: green; } ul > li { color: teal; } ol li { color: gray; }</style></head><body></body></html>"
val desc = br_style_block_rule_for_descendant(html, "ul", "li")
expect(desc.contains("color: green")).to_be_true()
expect(desc.contains("color: gray")).to_be_false()
expect(br_style_block_rule_for_descendant(html, "nav", "li")).to_equal("")
val child_out = br_style_block_rule_for_child(html, "ul", "li")
expect(child_out.contains("color: teal")).to_be_true()
expect(child_out.contains("color: green")).to_be_false()
expect(br_style_block_rule_for_child(html, "ol", "li")).to_equal("")
```

</details>

### css parser gpu tables — resolver selector matching

#### matches tag, class, id and universal selectors

- matches tag, class, id and universal selectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches tag, class, id and universal selectors")
val node = make_element("div", "btn primary", "main")
expect(selector_matches("div", node, nil, 1, 1)).to_be_true()
expect(selector_matches(".btn", node, nil, 1, 1)).to_be_true()
expect(selector_matches("#main", node, nil, 1, 1)).to_be_true()
expect(selector_matches("*", node, nil, 1, 1)).to_be_true()
expect(selector_matches("span", node, nil, 1, 1)).to_be_false()
expect(selector_matches(".ghost", node, nil, 1, 1)).to_be_false()
expect(selector_matches("#other", node, nil, 1, 1)).to_be_false()
```

</details>

#### matches compound and chained class selectors

- matches compound and chained class selectors


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches compound and chained class selectors")
val node = make_element("div", "btn primary", "main")
expect(selector_matches("div.btn", node, nil, 1, 1)).to_be_true()
expect(selector_matches("div#main", node, nil, 1, 1)).to_be_true()
expect(selector_matches(".btn.primary", node, nil, 1, 1)).to_be_true()
expect(selector_matches("span.btn", node, nil, 1, 1)).to_be_false()
expect(selector_matches(".btn.ghost", node, nil, 1, 1)).to_be_false()
```

</details>

#### matches positional pseudo-classes by nth and sibling count

- matches positional pseudo-classes by nth and sibling count


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches positional pseudo-classes by nth and sibling count")
val node = make_element("li", "", "")
expect(simple_selector_matches("li:first-child", node, 1, 3)).to_be_true()
expect(simple_selector_matches("li:first-child", node, 2, 3)).to_be_false()
expect(simple_selector_matches("li:last-child", node, 3, 3)).to_be_true()
expect(simple_selector_matches("li:only-child", node, 1, 1)).to_be_true()
expect(simple_selector_matches("li:only-child", node, 1, 2)).to_be_false()
expect(simple_selector_matches("li:nth-child(2)", node, 2, 4)).to_be_true()
expect(simple_selector_matches("li:nth-child(2)", node, 3, 4)).to_be_false()
```

</details>

#### matches nth-child keyword and formula arguments

- matches nth-child keyword and formula arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches nth-child keyword and formula arguments")
val node = make_element("li", "", "")
expect(simple_selector_matches("li:nth-child(odd)", node, 3, 5)).to_be_true()
expect(simple_selector_matches("li:nth-child(odd)", node, 2, 5)).to_be_false()
expect(simple_selector_matches("li:nth-child(even)", node, 2, 5)).to_be_true()
expect(simple_selector_matches("li:nth-child(2n+1)", node, 3, 5)).to_be_true()
expect(simple_selector_matches("li:nth-child(2n+1)", node, 4, 5)).to_be_false()
```

</details>

#### matches attribute selectors with exact and substring operators

- matches attribute selectors with exact and substring operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches attribute selectors with exact and substring operators")
val node = make_element("a", "", "")
node.set_attr("href", "https://example.test/docs/page")
expect(simple_selector_matches("a[href=\"https://example.test/docs/page\"]", node, 1, 1)).to_be_true()
expect(simple_selector_matches("a[href*=\"docs\"]", node, 1, 1)).to_be_true()
expect(simple_selector_matches("a[href*=\"admin\"]", node, 1, 1)).to_be_false()
expect(simple_selector_matches("a[href]", node, 1, 1)).to_be_true()
expect(simple_selector_matches("a[title]", node, 1, 1)).to_be_false()
```

</details>

#### matches :not and :is selector lists

- matches :not and :is selector lists


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches :not and :is selector lists")
val node = make_element("button", "secondary", "")
expect(simple_selector_matches(":not(.primary)", node, 1, 1)).to_be_true()
expect(simple_selector_matches(":not(.secondary)", node, 1, 1)).to_be_false()
expect(simple_selector_matches(":is(.primary, .secondary)", node, 1, 1)).to_be_true()
expect(simple_selector_matches(":is(.primary, .ghost)", node, 1, 1)).to_be_false()
```

</details>

#### rejects the child combinator without a matching parent

- rejects the child combinator without a matching parent
   - Expected: selector_matches(".parent > .child", child, nil, 1, 1) is false
   - Expected: selector_matches(".ghost > .child", child, nil, 1, 1) is false
   - Expected: selector_matches(".parent > ", child, nil, 1, 1) is false
   - Expected: selector_matches(" > .child", child, nil, 1, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects the child combinator without a matching parent")
# ENGINE LIMITATION (probed, not masked): under the seed test
# runner `match parent: case Some(x)` on a nullable parameter never
# matches a present value (probe: fn(p: text?) matching Some fails
# for probe("hello")), so neither the positive `.parent > .child`
# case nor any present-parent call can be asserted here. Only the
# nil-parent and malformed-selector rejection paths are stable.
val child = make_element("span", "child", "")
expect(selector_matches(".parent > .child", child, nil, 1, 1)).to_equal(false)
expect(selector_matches(".ghost > .child", child, nil, 1, 1)).to_equal(false)
expect(selector_matches(".parent > ", child, nil, 1, 1)).to_equal(false)
expect(selector_matches(" > .child", child, nil, 1, 1)).to_equal(false)
```

</details>

#### matches the descendant combinator by the subject selector

- matches the descendant combinator by the subject selector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the descendant combinator by the subject selector")
val node = make_element("span", "", "")
expect(selector_matches("div span", node, nil, 1, 1)).to_be_true()
expect(selector_matches("div em", node, nil, 1, 1)).to_be_false()
```

</details>

#### matches :empty only for childless elements

- matches :empty only for childless elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches :empty only for childless elements")
val node = make_element("div", "", "")
expect(simple_selector_matches("div:empty", node, 1, 1)).to_be_true()
val filled = make_element("div", "", "")
filled.children.push(BeDomNode.text("hello"))
expect(simple_selector_matches("div:empty", filled, 1, 1)).to_be_false()
```

</details>

### css parser gpu tables — cpu parity direct vs indexed lane

#### direct lane resolves the parity stylesheet correctly

- direct lane resolves the parity stylesheet correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("direct lane resolves the parity stylesheet correctly")
val node = make_element("div", "btn big", "main")
val direct = direct_matched_props(parity_css(), node, 1, 1)
expect(direct.contains("color:red")).to_be_true()
expect(direct.contains("width:100px")).to_be_true()
expect(direct.contains("margin-top:3px")).to_be_true()
expect(direct.contains("box-sizing:border-box")).to_be_true()
expect(direct.contains("color:navy")).to_be_true()
expect(direct.contains("padding-top:9px")).to_be_false()
```

</details>

#### multi-class table lane agrees with the direct lane on membership

- multi-class table lane agrees with the direct lane on membership
   - Expected: br_style_block_rule_for_multi_class(doc, "ghost zzz") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("multi-class table lane agrees with the direct lane on membership")
val doc = parity_doc()
# element with both classes: direct .btn.big matches, table entry non-empty
val both = make_element("div", "btn big", "")
expect(selector_matches(".btn.big", both, nil, 1, 1)).to_be_true()
val table_hit = br_style_block_rule_for_multi_class(doc, "btn big")
expect(table_hit.contains("color: navy")).to_be_true()
# element with unrelated classes: direct lane rejects, table lane empty
val other = make_element("div", "ghost zzz", "")
expect(selector_matches(".btn.big", other, nil, 1, 1)).to_be_false()
expect(br_style_block_rule_for_multi_class(doc, "ghost zzz")).to_equal("")
```

</details>

#### multi-class table declarations mirror direct lane declarations

- multi-class table declarations mirror direct lane declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("multi-class table declarations mirror direct lane declarations")
val doc = parity_doc()
val node = make_element("div", "btn big", "")
val rules = parse_css_rules(parity_css())
val indexed = br_style_block_rule_for_multi_class(doc, "btn big")
var i = 0
var checked = 0
while i < rules.len():
    val rule = rules[i]
    i = i + 1
    if rule.selector == ".btn.big":
        expect(selector_matches(rule.selector, node, nil, 1, 1)).to_be_true()
        var j = 0
        while j < rule.declarations.len():
            val d = rule.declarations[j]
            j = j + 1
            expect(indexed.contains(d.property)).to_be_true()
            expect(indexed.contains(d.value)).to_be_true()
            checked = checked + 1
expect(checked).to_be_greater_than(0)
```

</details>

#### matcher option lane agrees with the resolver on :not

- matcher option lane agrees with the resolver on :not
   - Expected: table_sec equals `direct_sec`
   - Expected: table_pri equals `direct_pri`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matcher option lane agrees with the resolver on :not")
val secondary_tag = "button class=\"secondary\""
val primary_tag = "button class=\"primary\""
val secondary = make_element("button", "secondary", "")
val primary = make_element("button", "primary", "")
val table_sec = br_selector_list_contains_not_self("button:not(button.primary)", "button", secondary_tag)
val direct_sec = simple_selector_matches(":not(.primary)", secondary, 1, 1)
expect(table_sec).to_equal(direct_sec)
expect(direct_sec).to_be_true()
val table_pri = br_selector_list_contains_not_self("button:not(button.primary)", "button", primary_tag)
val direct_pri = simple_selector_matches(":not(.primary)", primary, 1, 1)
expect(table_pri).to_equal(direct_pri)
expect(direct_pri).to_be_false()
```

</details>

#### matcher option lane agrees with the resolver on attribute substrings

- matcher option lane agrees with the resolver on attribute substrings
   - Expected: table_docs equals `direct_docs`
   - Expected: table_admin equals `direct_admin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matcher option lane agrees with the resolver on attribute substrings")
val docs_tag = "a href=\"https://example.test/docs/page\""
val docs_node = make_element("a", "", "")
docs_node.set_attr("href", "https://example.test/docs/page")
val table_docs = br_selector_list_contains_attr_self("a[href*=\"docs\"]", "a", docs_tag)
val direct_docs = simple_selector_matches("a[href*=\"docs\"]", docs_node, 1, 1)
expect(table_docs).to_equal(direct_docs)
expect(direct_docs).to_be_true()
val table_admin = br_selector_list_contains_attr_self("a[href*=\"admin\"]", "a", docs_tag)
val direct_admin = simple_selector_matches("a[href*=\"admin\"]", docs_node, 1, 1)
expect(table_admin).to_equal(direct_admin)
expect(direct_admin).to_be_false()
```

</details>

#### indexed simple-selector lanes agree with the direct lane

- indexed simple-selector lanes agree with the direct lane
   - Expected: br_style_block_rule_for_class(doc, "zz") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("indexed simple-selector lanes agree with the direct lane")
val doc = parity_doc()
val node = make_element("div", "btn big", "main")
val direct = direct_matched_props(parity_css(), node, 1, 1)
# class lane
expect(direct.contains("color:red")).to_be_true()
expect(br_style_block_rule_for_class(doc, "btn").contains("color: red")).to_be_true()
# id lane
expect(direct.contains("width:100px")).to_be_true()
expect(br_style_block_rule_for_id(doc, "main").contains("width: 100px")).to_be_true()
# tag lane
expect(direct.contains("margin-top:3px")).to_be_true()
expect(br_style_block_rule_for_tag(doc, "div").contains("margin-top: 3px")).to_be_true()
# universal lane
expect(direct.contains("box-sizing:border-box")).to_be_true()
expect(br_style_block_rule_for_universal(doc).contains("box-sizing: border-box")).to_be_true()
# both lanes reject the non-matching p rule and an absent class
expect(direct.contains("padding-top")).to_be_false()
expect(br_style_block_rule_for_class(doc, "btn").contains("padding-top")).to_be_false()
expect(selector_matches(".zz", node, nil, 1, 1)).to_be_false()
expect(br_style_block_rule_for_class(doc, "zz")).to_equal("")
```

</details>

#### indexed compound and combinator lanes agree with the direct lane where both run

- indexed compound and combinator lanes agree with the direct lane where both run
   - Expected: br_style_block_rule_for_tag_class(doc, "em", "btn") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("indexed compound and combinator lanes agree with the direct lane where both run")
val css = "div.btn { color: navy; } div#main { width: 7px; } " +
    "ul li { color: green; } ul > li { color: teal; }"
val doc = "<html><head><style>" + css + "</style></head><body></body></html>"
val node = make_element("div", "btn", "main")
expect(selector_matches("div.btn", node, nil, 1, 1)).to_be_true()
expect(br_style_block_rule_for_tag_class(doc, "div", "btn").contains("color: navy")).to_be_true()
expect(selector_matches("div#main", node, nil, 1, 1)).to_be_true()
expect(br_style_block_rule_for_tag_id(doc, "div", "main").contains("width: 7px")).to_be_true()
val li = make_element("li", "", "")
expect(selector_matches("ul li", li, nil, 1, 1)).to_be_true()
expect(br_style_block_rule_for_descendant(doc, "ul", "li").contains("color: green")).to_be_true()
# child combinator: the table lane surfaces the rule; the direct
# resolver rejects it without a matching parent (nil-parent
# limitation documented above)
expect(br_style_block_rule_for_child(doc, "ul", "li").contains("color: teal")).to_be_true()
expect(selector_matches("ul > li", li, nil, 1, 1)).to_be_false()
# miss direction agrees on both lanes
expect(selector_matches("em.btn", node, nil, 1, 1)).to_be_false()
expect(br_style_block_rule_for_tag_class(doc, "em", "btn")).to_equal("")
```

</details>

### css parser gpu tables — shorthand declaration expansion

#### expands the flex shorthand across every arity form

- expands the flex shorthand across every arity form


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands the flex shorthand across every arity form")
expect(decl_pairs("flex: none")).to_equal(
    "flex-grow=0;flex-shrink=0;flex-basis=auto;")
expect(decl_pairs("flex: 2")).to_equal(
    "flex-grow=2;flex-shrink=1;flex-basis=0%;")
expect(decl_pairs("flex: 3 4")).to_equal(
    "flex-grow=3;flex-shrink=4;flex-basis=0%;")
expect(decl_pairs("flex: 5 6 120px")).to_equal(
    "flex-grow=5;flex-shrink=6;flex-basis=120px;")
```

</details>

#### routes flex-flow through the shorthand dispatcher

- routes flex-flow through the shorthand dispatcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes flex-flow through the shorthand dispatcher")
expect(decl_pairs("flex-flow: column wrap-reverse")).to_equal(
    "flex-direction=column;flex-wrap=wrap-reverse;")
```

</details>

#### expands the border shorthand and normalizes keyword widths

- expands the border shorthand and normalizes keyword widths


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands the border shorthand and normalizes keyword widths")
expect(decl_pairs("border: 2px dashed blue")).to_equal(
    "border-width=2px;border-style=dashed;border-color=blue;")
expect(decl_pairs("border: thin solid red")).to_equal(
    "border-width=1px;border-style=solid;border-color=red;")
expect(decl_pairs("border: medium dotted red")).to_equal(
    "border-width=3px;border-style=dotted;border-color=red;")
expect(decl_pairs("border: thick double red")).to_equal(
    "border-width=5px;border-style=double;border-color=red;")
expect(decl_pairs("border: 0.5em none red")).to_equal(
    "border-width=0.5em;border-style=none;border-color=red;")
# a lone color keeps the 1px/solid defaults
expect(decl_pairs("border: green")).to_equal(
    "border-width=1px;border-style=solid;border-color=green;")
```

</details>

#### lifts a background color out of the background shorthand

- lifts a background color out of the background shorthand
   - Expected: decl_pairs("background: red") equals `background-color=red;`
   - Expected: decl_pairs("background: black") equals `background-color=black;`
   - Expected: decl_pairs("background: #ff0000") equals `background-color=#ff0000;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lifts a background color out of the background shorthand")
expect(decl_pairs("background: red")).to_equal("background-color=red;")
expect(decl_pairs("background: black")).to_equal("background-color=black;")
expect(decl_pairs("background: #ff0000")).to_equal("background-color=#ff0000;")
expect(decl_pairs("background: transparent")).to_equal(
    "background-color=transparent;")
# a functional color token is kept whole across its inner spaces
expect(decl_pairs("background: rgba(1, 2, 3, 0.5) fixed")).to_equal(
    "background-color=rgba(1, 2, 3, 0.5);")
# url() and non-color keywords are skipped; the trailing hex wins
expect(decl_pairs("background: url(a.png) no-repeat #00ff00")).to_equal(
    "background-color=#00ff00;")
```

</details>

#### leaves a background with no usable color as the untouched shorthand

- leaves a background with no usable color as the untouched shorthand
   - Expected: decl_pairs("background: no-repeat") equals `background=no-repeat;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves a background with no usable color as the untouched shorthand")
expect(decl_pairs("background: linear-gradient(red, blue)")).to_equal(
    "background=linear-gradient(red, blue);")
expect(decl_pairs("background: no-repeat")).to_equal("background=no-repeat;")
```

</details>

#### extracts a font-size and font-weight from the font shorthand

- extracts a font-size and font-weight from the font shorthand
   - Expected: decl_pairs("font: 1.5rem Georgia") equals `font-size=1.5rem;`
   - Expected: decl_pairs("font: italic 120%") equals `font-size=120%;`
   - Expected: decl_pairs("font: serif") equals `font=serif;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts a font-size and font-weight from the font shorthand")
expect(decl_pairs("font: bold 12px Arial")).to_equal(
    "font-weight=bold;font-size=12px;")
expect(decl_pairs("font: 1.5rem Georgia")).to_equal("font-size=1.5rem;")
expect(decl_pairs("font: italic 120%")).to_equal("font-size=120%;")
# nothing recognizable: the shorthand survives as-is
expect(decl_pairs("font: serif")).to_equal("font=serif;")
```

</details>

#### expands margin and padding box shorthands by arity

- expands margin and padding box shorthands by arity
   - Expected: decl_pairs("margin: 5px") equals `margin=5px;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands margin and padding box shorthands by arity")
expect(decl_pairs("margin: 5px")).to_equal("margin=5px;")
expect(decl_pairs("margin: 1px 2px")).to_equal(
    "margin-top=1px;margin-right=2px;margin-bottom=1px;margin-left=2px;")
expect(decl_pairs("padding: 1px 2px 3px")).to_equal(
    "padding-top=1px;padding-right=2px;padding-bottom=3px;padding-left=2px;")
expect(decl_pairs("padding: 1px 2px 3px 4px")).to_equal(
    "padding-top=1px;padding-right=2px;padding-bottom=3px;padding-left=4px;")
```

</details>

### css parser gpu tables — :has() relational matching

#### matches :has() against direct children and deeper descendants

- matches :has() against direct children and deeper descendants


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches :has() against direct children and deeper descendants")
val root = has_fixture_tree()
expect(simple_selector_matches(":has(h2)", root, 1, 1)).to_be_true()
expect(simple_selector_matches(":has(li)", root, 1, 1)).to_be_true()
expect(simple_selector_matches(":has(.hot)", root, 1, 1)).to_be_true()
expect(simple_selector_matches(":has(span)", root, 1, 1)).to_be_false()
```

</details>

#### honors the child combinator inside :has()

- honors the child combinator inside :has()


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("honors the child combinator inside :has()")
val root = has_fixture_tree()
expect(simple_selector_matches(":has(> h2)", root, 1, 1)).to_be_true()
expect(simple_selector_matches(":has(> ul)", root, 1, 1)).to_be_true()
# li is a grandchild, so the child form must reject it even though
# the descendant form above accepts it
expect(simple_selector_matches(":has(> li)", root, 1, 1)).to_be_false()
# a bare ">" has no selector after it
expect(simple_selector_matches(":has(>)", root, 1, 1)).to_be_false()
```

</details>

#### treats the :has() argument as a forgiving selector list

- treats the :has() argument as a forgiving selector list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats the :has() argument as a forgiving selector list")
val root = has_fixture_tree()
expect(simple_selector_matches(":has(span, ul)", root, 1, 1)).to_be_true()
expect(simple_selector_matches(":has(span, em)", root, 1, 1)).to_be_false()
# unterminated argument: no closing paren, no match
expect(simple_selector_matches(":has(ul", root, 1, 1)).to_be_false()
```

</details>

#### combines a compound base selector with :has()

- combines a compound base selector with :has()


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("combines a compound base selector with :has()")
val root = has_fixture_tree()
expect(simple_selector_matches("div:has(ul)", root, 1, 1)).to_be_true()
expect(simple_selector_matches("p:has(ul)", root, 1, 1)).to_be_false()
expect(simple_selector_matches("div:has(span)", root, 1, 1)).to_be_false()
```

</details>

### css parser gpu tables — attribute and positional selector edges

#### matches the ~= whitespace-token and $= suffix attribute operators

- matches the ~= whitespace-token and $= suffix attribute operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the ~= whitespace-token and $= suffix attribute operators")
val chip = make_element("span", "", "")
chip.set_attr("data-tags", "alpha beta gamma")
chip.set_attr("href", "/docs/index.html")
expect(simple_selector_matches("span[data-tags~=beta]", chip, 1, 1)).to_be_true()
expect(simple_selector_matches("span[data-tags~=alpha]", chip, 1, 1)).to_be_true()
expect(simple_selector_matches("span[data-tags~=delta]", chip, 1, 1)).to_be_false()
expect(simple_selector_matches("span[href$=\".html\"]", chip, 1, 1)).to_be_true()
expect(simple_selector_matches("span[href$=\".css\"]", chip, 1, 1)).to_be_false()
```

</details>

#### rejects an attribute selector with an empty key

- rejects an attribute selector with an empty key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an attribute selector with an empty key")
val chip = make_element("span", "", "")
chip.set_attr("data-tags", "alpha")
expect(simple_selector_matches("span[=alpha]", chip, 1, 1)).to_be_false()
```

</details>

#### matches :first-child and the -n+3 nth-child formula

- matches :first-child and the -n+3 nth-child formula


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches :first-child and the -n+3 nth-child formula")
val chip = make_element("span", "", "")
expect(simple_selector_matches(":first-child", chip, 1, 3)).to_be_true()
expect(simple_selector_matches(":first-child", chip, 2, 3)).to_be_false()
expect(simple_selector_matches("span:nth-child(-n+3)", chip, 2, 5)).to_be_true()
expect(simple_selector_matches("span:nth-child(-n+3)", chip, 4, 5)).to_be_false()
```

</details>

#### combines a compound base selector with :not() and :is()

- combines a compound base selector with :not() and :is()


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("combines a compound base selector with :not() and :is()")
val btn = make_element("button", "primary", "")
expect(simple_selector_matches("button:not(.ghost)", btn, 1, 1)).to_be_true()
expect(simple_selector_matches("button:not(.primary)", btn, 1, 1)).to_be_false()
# an empty :not() list matches nothing
expect(simple_selector_matches("button:not()", btn, 1, 1)).to_be_false()
expect(simple_selector_matches("button:is(.primary, .ghost)", btn, 1, 1)).to_be_true()
expect(simple_selector_matches("button:is(.ghost, .muted)", btn, 1, 1)).to_be_false()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering css parser gpu tables — style block parsing, css parser gpu tables — selector matcher, css parser gpu tables — rule index tables, css parser gpu tables — resolver selector matching, css parser gpu tables — cpu parity direct vs indexed lane, css parser gpu tables — shorthand declaration expansion, css parser gpu tables — :has() relational matching, css parser gpu tables — attribute and positional selector edges.
- css parser gpu tables — style block parsing
- css parser gpu tables — selector matcher
- css parser gpu tables — rule index tables
- css parser gpu tables — resolver selector matching
- css parser gpu tables — cpu parity direct vs indexed lane
- css parser gpu tables — shorthand declaration expansion
- css parser gpu tables — :has() relational matching
- css parser gpu tables — attribute and positional selector edges

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 62 |
| Active scenarios | 62 |
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

- Canonical SPipe generation for source `eeba7b09afc7b8a2fa4dda51428f66d1a5614e82dea732f8869954ed1f5d5f77`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eeba7b09afc7b8a2fa4dda51428f66d1a5614e82dea732f8869954ed1f5d5f77`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eeba7b09afc7b8a2fa4dda51428f66d1a5614e82dea732f8869954ed1f5d5f77`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts multiple style blocks from html' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns no blocks when html has no style element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_parser_gpu_tables_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a simple rule into selector and declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
