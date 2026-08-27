# Blink CSS Parser Specification

> Purpose: Prove that parse_css.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink CSS Parser Specification

Purpose: Prove that parse_css.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/unit/lib/blink/css_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that parse_css.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### parse_css

#### empty token list produces empty stylesheet

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty token list produces empty stylesheet
- Verify: empty token list produces empty stylesheet
   - Expected: sheet.rules.len() equals `0`
   - Expected: sheet.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty token list produces empty stylesheet")
step("Verify: empty token list produces empty stylesheet")
# @req: REQ-LIB-BLINK-001
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Eof, text: "", line: 1, column: 1)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(sheet.errors.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### single rule \

- single rule \
   - Expected: sheet.rules.len() equals `1`
   - Expected: rule.selector equals `.foo`
   - Expected: rule.declarations.len() equals `1`
   - Expected: decl.property equals `color`
   - Expected: decl.value equals `red`
   - Expected: not_important is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single rule \")
# Tokens: Delim(".") Identifier("foo") Delim("{") Identifier("color") Delim(":") Identifier("red") Delim(";") Delim("}") Eof
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Delim,      text: ".",     line: 1, column: 1),
    CssToken(kind: CssTokenKind.Identifier,  text: "foo",  line: 1, column: 2),
    CssToken(kind: CssTokenKind.Delim,       text: "{",    line: 1, column: 6),
    CssToken(kind: CssTokenKind.Identifier,  text: "color",line: 1, column: 8),
    CssToken(kind: CssTokenKind.Delim,       text: ":",    line: 1, column: 13),
    CssToken(kind: CssTokenKind.Identifier,  text: "red",  line: 1, column: 15),
    CssToken(kind: CssTokenKind.Delim,       text: ";",    line: 1, column: 18),
    CssToken(kind: CssTokenKind.Delim,       text: "}",    line: 1, column: 20),
    CssToken(kind: CssTokenKind.Eof,         text: "",     line: 1, column: 21)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val rule = sheet.rules[0]
expect(rule.selector).to_equal(".foo")
expect(rule.declarations.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val decl = rule.declarations[0]
expect(decl.property).to_equal("color")
expect(decl.value).to_equal("red")
val not_important = decl.important == false
expect(not_important).to_equal(true)
```

</details>

#### rule with multiple declarations produces correct count

- rule with multiple declarations produces correct count
- Verify: rule with multiple declarations produces correct count
   - Expected: sheet.rules.len() equals `1`
   - Expected: sheet.rules[0].declarations.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rule with multiple declarations produces correct count")
step("Verify: rule with multiple declarations produces correct count")
# .bar { margin: 0; padding: 4px; display: flex; }
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Delim,      text: ".",       line: 1, column: 1),
    CssToken(kind: CssTokenKind.Identifier,  text: "bar",    line: 1, column: 2),
    CssToken(kind: CssTokenKind.Delim,       text: "{",      line: 1, column: 6),
    CssToken(kind: CssTokenKind.Identifier,  text: "margin", line: 1, column: 8),
    CssToken(kind: CssTokenKind.Delim,       text: ":",      line: 1, column: 14),
    CssToken(kind: CssTokenKind.Number,      text: "0",      line: 1, column: 16),
    CssToken(kind: CssTokenKind.Delim,       text: ";",      line: 1, column: 17),
    CssToken(kind: CssTokenKind.Identifier,  text: "padding",line: 1, column: 19),
    CssToken(kind: CssTokenKind.Delim,       text: ":",      line: 1, column: 26),
    CssToken(kind: CssTokenKind.Identifier,  text: "4px",   line: 1, column: 28),
    CssToken(kind: CssTokenKind.Delim,       text: ";",      line: 1, column: 31),
    CssToken(kind: CssTokenKind.Identifier,  text: "display",line: 1, column: 33),
    CssToken(kind: CssTokenKind.Delim,       text: ":",      line: 1, column: 40),
    CssToken(kind: CssTokenKind.Identifier,  text: "flex",   line: 1, column: 42),
    CssToken(kind: CssTokenKind.Delim,       text: ";",      line: 1, column: 46),
    CssToken(kind: CssTokenKind.Delim,       text: "}",      line: 1, column: 48),
    CssToken(kind: CssTokenKind.Eof,         text: "",       line: 1, column: 49)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(sheet.rules[0].declarations.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### declaration with !important sets important=true

- declaration with !important sets important=true
- Verify: declaration with !important sets important=true
   - Expected: sheet.rules.len() equals `1`
   - Expected: decl.value equals `blue`
   - Expected: decl.important is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declaration with !important sets important=true")
step("Verify: declaration with !important sets important=true")
# h1 { color: blue !important; }
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Identifier,  text: "h1",        line: 1, column: 1),
    CssToken(kind: CssTokenKind.Delim,       text: "{",         line: 1, column: 4),
    CssToken(kind: CssTokenKind.Identifier,  text: "color",     line: 1, column: 6),
    CssToken(kind: CssTokenKind.Delim,       text: ":",         line: 1, column: 11),
    CssToken(kind: CssTokenKind.Identifier,  text: "blue",      line: 1, column: 13),
    CssToken(kind: CssTokenKind.Delim,       text: "!",         line: 1, column: 18),
    CssToken(kind: CssTokenKind.Identifier,  text: "important", line: 1, column: 19),
    CssToken(kind: CssTokenKind.Delim,       text: ";",         line: 1, column: 28),
    CssToken(kind: CssTokenKind.Delim,       text: "}",         line: 1, column: 30),
    CssToken(kind: CssTokenKind.Eof,         text: "",          line: 1, column: 31)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val decl = sheet.rules[0].declarations[0]
expect(decl.value).to_equal("blue")
expect(decl.important).to_equal(true)
```

</details>

#### two rules produces 2 CssStyleRule entries

- two rules produces 2 CssStyleRule entries
- Verify: two rules produces 2 CssStyleRule entries
   - Expected: sheet.rules.len() equals `2`
   - Expected: sheet.rules[0].selector equals `a`
   - Expected: sheet.rules[1].selector equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two rules produces 2 CssStyleRule entries")
step("Verify: two rules produces 2 CssStyleRule entries")
# a { color: red; } b { color: blue; }
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Identifier,  text: "a",     line: 1, column: 1),
    CssToken(kind: CssTokenKind.Delim,       text: "{",     line: 1, column: 3),
    CssToken(kind: CssTokenKind.Identifier,  text: "color", line: 1, column: 5),
    CssToken(kind: CssTokenKind.Delim,       text: ":",     line: 1, column: 10),
    CssToken(kind: CssTokenKind.Identifier,  text: "red",   line: 1, column: 12),
    CssToken(kind: CssTokenKind.Delim,       text: ";",     line: 1, column: 15),
    CssToken(kind: CssTokenKind.Delim,       text: "}",     line: 1, column: 17),
    CssToken(kind: CssTokenKind.Identifier,  text: "b",     line: 2, column: 1),
    CssToken(kind: CssTokenKind.Delim,       text: "{",     line: 2, column: 3),
    CssToken(kind: CssTokenKind.Identifier,  text: "color", line: 2, column: 5),
    CssToken(kind: CssTokenKind.Delim,       text: ":",     line: 2, column: 10),
    CssToken(kind: CssTokenKind.Identifier,  text: "blue",  line: 2, column: 12),
    CssToken(kind: CssTokenKind.Delim,       text: ";",     line: 2, column: 16),
    CssToken(kind: CssTokenKind.Delim,       text: "}",     line: 2, column: 18),
    CssToken(kind: CssTokenKind.Eof,         text: "",      line: 2, column: 19)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(sheet.rules[0].selector).to_equal("a")
expect(sheet.rules[1].selector).to_equal("b")
```

</details>

#### malformed input (missing {) records error, skips, continues

- malformed input (missing {) records error, skips, continues
- Verify: malformed input (missing () records error, skips, continues
   - Expected: sheet.rules.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("malformed input (missing {) records error, skips, continues")
step("Verify: malformed input (missing () records error, skips, continues")
# "color red" with no braces — missing `{`, then a valid rule "p { font: sans; }"
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Identifier,  text: "color", line: 1, column: 1),
    CssToken(kind: CssTokenKind.Identifier,  text: "red",   line: 1, column: 7),
    CssToken(kind: CssTokenKind.Eof,         text: "",      line: 1, column: 10)
]
val sheet = parse_css(tokens)
# Reaches Eof without `{` — error should be recorded, no rules
expect(sheet.errors.len()).to_be_greater_than(0)
expect(sheet.rules.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### property and value text are extracted correctly

- property and value text are extracted correctly
- Verify: property and value text are extracted correctly
   - Expected: sheet.rules.len() equals `1`
   - Expected: decl.property equals `background-color`
   - Expected: decl.value equals `#336699`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("property and value text are extracted correctly")
step("Verify: property and value text are extracted correctly")
# div { background-color: #336699; }
# Hash token strips the `#`; the parser restores it when rejoining.
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Identifier,  text: "div",             line: 1, column: 1),
    CssToken(kind: CssTokenKind.Delim,       text: "{",               line: 1, column: 5),
    CssToken(kind: CssTokenKind.Identifier,  text: "background-color",line: 1, column: 7),
    CssToken(kind: CssTokenKind.Delim,       text: ":",               line: 1, column: 23),
    CssToken(kind: CssTokenKind.Hash,        text: "336699",          line: 1, column: 25),
    CssToken(kind: CssTokenKind.Delim,       text: ";",               line: 1, column: 31),
    CssToken(kind: CssTokenKind.Delim,       text: "}",               line: 1, column: 33),
    CssToken(kind: CssTokenKind.Eof,         text: "",                line: 1, column: 34)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val decl = sheet.rules[0].declarations[0]
expect(decl.property).to_equal("background-color")
expect(decl.value).to_equal("#336699")
```

</details>

### tokenize_css + parse_css — whitespace is significant (CSS Syntax Level 3)

#### \

- \
   - Expected: sheet.rules.len() equals `1`
   - Expected: sheet.rules[0].selector equals `div .foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
# A real space between "div" and ".foo" is the descendant combinator —
# it must survive tokenize_css -> parse_css as "div .foo", distinct
# from the compound selector "div.foo" below. Before the fix, the
# tokenizer never emitted a Whitespace token so both spellings
# collapsed to the identical selector string "div.foo".
val source = "div .foo { color: red; }"
val tokens = tokenize_css(source)
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(sheet.rules[0].selector).to_equal("div .foo")
```

</details>

#### \

- \
   - Expected: sheet.rules.len() equals `1`
   - Expected: sheet.rules[0].selector equals `div.foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
val source = "div.foo { color: red; }"
val tokens = tokenize_css(source)
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(sheet.rules[0].selector).to_equal("div.foo")
```

</details>

#### descendant selector and compound selector parse to DIFFERENT selector text

- descendant selector and compound selector parse to DIFFERENT selector text
- Verify: descendant selector and compound selector parse to DIFFERENT selector text
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("descendant selector and compound selector parse to DIFFERENT selector text")
step("Verify: descendant selector and compound selector parse to DIFFERENT selector text")
# This is the regression itself: both used to serialize identically.
val descendant = parse_css(tokenize_css("div .foo { color: red; }"))
val compound = parse_css(tokenize_css("div.foo { color: red; }"))
val same = descendant.rules[0].selector == compound.rules[0].selector
expect(same).to_equal(false)
```

</details>

#### \

- \
   - Expected: sheet.rules.len() equals `1`
   - Expected: sheet.rules[0].selector equals `div * p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
# '*' was previously in _attaches_forward, so "div * p" collapsed to
# "div *p" — a broken universal-descendant selector.
val source = "div * p { color: blue; }"
val tokens = tokenize_css(source)
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(sheet.rules[0].selector).to_equal("div * p")
```

</details>

#### \

- \
   - Expected: sheet.rules.len() equals `1`
   - Expected: sheet.rules[0].declarations[0].value equals `rgb(1, 2, 3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
# ',' was in neither adjacency predicate, so "rgb(1, 2, 3)" used to
# rejoin as "rgb(1 , 2 , 3)" (space BEFORE each comma, none after).
val source = "a { color: rgb(1, 2, 3); }"
val tokens = tokenize_css(source)
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(sheet.rules[0].declarations[0].value).to_equal("rgb(1, 2, 3)")
```

</details>

#### \

- \
   - Expected: sheet.rules.len() equals `1`
   - Expected: sheet.rules[0].declarations[0].value equals `calc(1px * 2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
val source = "a { width: calc(1px * 2); }"
val tokens = tokenize_css(source)
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(sheet.rules[0].declarations[0].value).to_equal("calc(1px * 2)")
```

</details>

#### declaration value \

- declaration value \
   - Expected: sheet.rules[0].declarations[0].value equals `1px solid red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declaration value \")
val source = "a { border: 1px solid red; }"
val tokens = tokenize_css(source)
val sheet = parse_css(tokens)
expect(sheet.rules[0].declarations[0].value).to_equal("1px solid red")
```

</details>

#### \

- \
   - Expected: decl.value equals `blue`
   - Expected: decl.important is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("\")
val source = "h1 { color: blue !important; }"
val tokens = tokenize_css(source)
val sheet = parse_css(tokens)
val decl = sheet.rules[0].declarations[0]
expect(decl.value).to_equal("blue")
expect(decl.important).to_equal(true)
```

</details>

#### end-to-end: 'div .foo { ... }' selector text matches a DOM structure that 'div.foo { ... }' does NOT

- end-to-end: 'div .foo { ... }' selector text matches a DOM structure that 'div.foo { ... }' does NOT
- build document > div > p.foo — p carries class 'foo', nested inside div
- parse both rules through the real tokenizer/parser pipeline
- 'div .foo' (descendant) matches the nested p.foo
   - Expected: matches_complex(tree, p_id, descendant_sel) is true
- 'div.foo' (compound) does NOT match — p is not itself a div
   - Expected: matches_complex(tree, p_id, compound_sel) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("end-to-end: 'div .foo { ... }' selector text matches a DOM structure that 'div.foo { ... }' does NOT")
# This is the payoff of the fix, chained through the full pipeline:
# source text -> tokenize_css -> parse_css (selector reconstruction)
# -> parse_selector -> matches_complex. Before the fix, both rules'
# selector strings were identical ("div.foo"), so this distinction
# was impossible to observe.
step("build document > div > p.foo — p carries class 'foo', nested inside div")
var tree = dom_tree_new()
val div_id = tree.create_element("div")
val p_id = tree.create_element("p")
tree.append_child(0, div_id)
tree.append_child(div_id, p_id)
tree.set_attribute(p_id, "class", "foo")

step("parse both rules through the real tokenizer/parser pipeline")
val descendant_sheet = parse_css(tokenize_css("div .foo { color: red; }"))
val compound_sheet = parse_css(tokenize_css("div.foo { color: red; }"))
val descendant_sel = parse_selector(descendant_sheet.rules[0].selector).unwrap()
val compound_sel = parse_selector(compound_sheet.rules[0].selector).unwrap()

step("'div .foo' (descendant) matches the nested p.foo")
expect(matches_complex(tree, p_id, descendant_sel)).to_equal(true)
step("'div.foo' (compound) does NOT match — p is not itself a div")
expect(matches_complex(tree, p_id, compound_sel)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-BLINK-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d108cb291565df36952f755bea9928738a5b1817886d3cab1de1c475f253d26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d108cb291565df36952f755bea9928738a5b1817886d3cab1de1c475f253d26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d108cb291565df36952f755bea9928738a5b1817886d3cab1de1c475f253d26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/blink/css_parser_spec.spl
mirror: doc/06_spec/unit/lib/blink/css_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/blink/css_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/css_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/css_parser_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty token list produces empty stylesheet' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/css_parser_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single rule \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/css_parser_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rule with multiple declarations produces correct count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
