# Web Parser Specification

> Tests covering bounded tiny HTML tokenizer and parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Parser Specification

## Scenarios

### bounded tiny HTML tokenizer and parser

#### parses admitted body div text button and input nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### reports unsupported tags without pretending full support

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = tiny_web_parse("<body><script>x</script><p>ok</p></body>", 16, 8, 64)
expect(parsed.status.is_ok()).to_be(false)
expect(parsed.unsupported_count).to_equal(2)
expect(parsed.nodes.len()).to_be_greater_than(2)
```

</details>

#### admits the bounded document heading list link label and break vocabulary

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = tiny_web_parse("<html><head><title>T</title></head><body><h1>H</h1><label>L</label><ul><li><a href='/x'>X</a><br></li></ul></body></html>", 32, 12, 128)
expect(parsed.status.is_ok()).to_be(true)
expect(parsed.nodes[3].kind).to_equal(TINY_WEB_TITLE)
expect(parsed.nodes[5].kind).to_equal(TINY_WEB_HEADING)
expect(parsed.nodes[7].kind).to_equal(TINY_WEB_LABEL)
expect(parsed.nodes[10].kind).to_equal(TINY_WEB_LI)
expect(parsed.nodes[11].kind).to_equal(TINY_WEB_A)
expect(parsed.nodes[13].kind).to_equal(TINY_WEB_BR)
```

</details>

#### preserves admitted control and selector attributes while suppressing metadata text

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = tiny_web_parse("<html><head><title>Product</title><style>.primary { color: blue }</style></head><body><input id='name' class='primary field' type='text' name='user' value='Ada' placeholder='Name' maxlength='12' disabled><input type='checkbox' checked><a href='/next'>Next</a></body></html>", 24, 10, 384)
expect(parsed.status.is_ok()).to_be(true)
expect(parsed.title_text).to_equal("Product")
expect(parsed.style_source).to_contain(".primary")
expect(parsed.nodes[6].id_value).to_equal("name")
expect(parsed.nodes[6].class_value).to_equal("primary field")
expect(parsed.nodes[6].type_value).to_equal("text")
expect(parsed.nodes[6].value_attribute).to_equal("Ada")
expect(parsed.nodes[6].name_value).to_equal("user")
expect(parsed.nodes[6].placeholder_value).to_equal("Name")
expect(parsed.nodes[6].max_length_value).to_equal("12")
expect(parsed.nodes[6].disabled).to_be(true)
expect(parsed.nodes[7].checked).to_be(true)
expect(parsed.nodes[8].href_value).to_equal("/next")
var metadata_text_rendered = false
for node in parsed.nodes:
    if node.kind == TINY_WEB_TEXT and (node.text_value == "Product" or node.text_value.contains("primary")):
        metadata_text_rendered = true
expect(metadata_text_rendered).to_be(false)
```

</details>

#### suppresses unsupported subtrees and their text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = tiny_web_parse("<body><script><span>secret</span></script><p>shown</p></body>", 20, 8, 128)
expect(parsed.status.is_ok()).to_be(false)
expect(parsed.unsupported_count).to_equal(4)
expect(parsed.nodes.len()).to_equal(4)
expect(parsed.nodes[3].text_value).to_equal("shown")
```

</details>

#### reports malformed input and bounded capacities

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tiny_html_tokenize("<body", 8, 64).status.is_ok()).to_be(false)
expect(tiny_web_parse("<body><div></body>", 8, 8, 64).status.is_ok()).to_be(false)
expect(tiny_web_parse("<body><div><p>x</p></div></body>", 3, 8, 64).status.is_ok()).to_be(false)
expect(tiny_web_parse("<body>long text</body>", 8, 8, 3).status.is_ok()).to_be(false)
expect(tiny_web_parse("<body><div><p>x</p></div></body>", 12, 1, 64).status.is_ok()).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/web_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bounded tiny HTML tokenizer and parser.
- bounded tiny HTML tokenizer and parser

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f1727caf09b781fb077477f27be5c849edd049d845baaa8e28346975d8d0714`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f1727caf09b781fb077477f27be5c849edd049d845baaa8e28346975d8d0714`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f1727caf09b781fb077477f27be5c849edd049d845baaa8e28346975d8d0714`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/lib/tiny/web_parser_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/web_parser_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/web_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/web_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/tiny/web_parser_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/tiny/web_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/tiny/web_parser_spec.spl:15:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses admitted body div text button and input nodes' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_parser_spec.spl:27:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports unsupported tags without pretending full support' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_parser_spec.spl:33:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'admits the bounded document heading list link label and break vocabulary' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_parser_spec.spl:43:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'preserves admitted control and selector attributes while suppressing metadata text' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
