# web_parser_spec

> Verifies the web parser behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_parser_spec

Verifies the web parser behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/web_parser_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the web parser behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### bounded tiny HTML tokenizer and parser

#### parses admitted body div text button and input nodes

- Verify: parses admitted body div text button and input nodes
   - Expected: parsed.nodes.len() equals `7)  # oracle: pinned constant asserted by this scenario`
   - Expected: parsed.nodes[1].kind equals `TINY_WEB_BODY`
   - Expected: parsed.nodes[2].kind equals `TINY_WEB_DIV`
   - Expected: parsed.nodes[3].kind equals `TINY_WEB_TEXT`
   - Expected: parsed.nodes[4].kind equals `TINY_WEB_BUTTON`
   - Expected: parsed.nodes[6].kind equals `TINY_WEB_INPUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PARSER-001
step("Verify: parses admitted body div text button and input nodes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parsed = tiny_web_parse("<body><div>Hello<button>Go</button><input></div></body>", 16, 8, 64)
expect(parsed.status.is_ok()).to_be(true)
expect(parsed.nodes.len()).to_equal(7)  # oracle: pinned constant asserted by this scenario
expect(parsed.nodes[1].kind).to_equal(TINY_WEB_BODY)
expect(parsed.nodes[2].kind).to_equal(TINY_WEB_DIV)
expect(parsed.nodes[3].kind).to_equal(TINY_WEB_TEXT)
expect(parsed.nodes[4].kind).to_equal(TINY_WEB_BUTTON)
expect(parsed.nodes[6].kind).to_equal(TINY_WEB_INPUT)
```

</details>

#### reports unsupported tags without pretending full support

- Verify: reports unsupported tags without pretending full support
   - Expected: parsed.unsupported_count equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PARSER-001
step("Verify: reports unsupported tags without pretending full support")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parsed = tiny_web_parse("<body><script>x</script><p>ok</p></body>", 16, 8, 64)
expect(parsed.status.is_ok()).to_be(false)
expect(parsed.unsupported_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(parsed.nodes.len()).to_be_greater_than(2)
```

</details>

#### admits the bounded document heading list link label and break vocabulary

- Verify: admits the bounded document heading list link label and break vocabulary
   - Expected: parsed.nodes[3].kind equals `TINY_WEB_TITLE`
   - Expected: parsed.nodes[5].kind equals `TINY_WEB_HEADING`
   - Expected: parsed.nodes[7].kind equals `TINY_WEB_LABEL`
   - Expected: parsed.nodes[10].kind equals `TINY_WEB_LI`
   - Expected: parsed.nodes[11].kind equals `TINY_WEB_A`
   - Expected: parsed.nodes[13].kind equals `TINY_WEB_BR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PARSER-001
step("Verify: admits the bounded document heading list link label and break vocabulary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: preserves admitted control and selector attributes while suppressing metadata text
   - Expected: parsed.title_text equals `Product`
   - Expected: parsed.nodes[6].id_value equals `name`
   - Expected: parsed.nodes[6].class_value equals `primary field`
   - Expected: parsed.nodes[6].type_value equals `text`
   - Expected: parsed.nodes[6].value_attribute equals `Ada`
   - Expected: parsed.nodes[6].name_value equals `user`
   - Expected: parsed.nodes[6].placeholder_value equals `Name`
   - Expected: parsed.nodes[6].max_length_value equals `12`
   - Expected: parsed.nodes[8].href_value equals `/next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PARSER-001
step("Verify: preserves admitted control and selector attributes while suppressing metadata text")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: suppresses unsupported subtrees and their text
   - Expected: parsed.unsupported_count equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: parsed.nodes.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: parsed.nodes[3].text_value equals `shown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PARSER-001
step("Verify: suppresses unsupported subtrees and their text")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parsed = tiny_web_parse("<body><script><span>secret</span></script><p>shown</p></body>", 20, 8, 128)
expect(parsed.status.is_ok()).to_be(false)
expect(parsed.unsupported_count).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(parsed.nodes.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(parsed.nodes[3].text_value).to_equal("shown")
```

</details>

#### reports malformed input and bounded capacities

- Verify: reports malformed input and bounded capacities


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PARSER-001
step("Verify: reports malformed input and bounded capacities")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(tiny_html_tokenize("<body", 8, 64).status.is_ok()).to_be(false)
expect(tiny_web_parse("<body><div></body>", 8, 8, 64).status.is_ok()).to_be(false)
expect(tiny_web_parse("<body><div><p>x</p></div></body>", 3, 8, 64).status.is_ok()).to_be(false)
expect(tiny_web_parse("<body>long text</body>", 8, 8, 3).status.is_ok()).to_be(false)
expect(tiny_web_parse("<body><div><p>x</p></div></body>", 12, 1, 64).status.is_ok()).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7278de598b1ff372ec1f70e1a6ba450cc7793710731a4d413db49ad8dc38ba33`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7278de598b1ff372ec1f70e1a6ba450cc7793710731a4d413db49ad8dc38ba33`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7278de598b1ff372ec1f70e1a6ba450cc7793710731a4d413db49ad8dc38ba33`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/tiny/web_parser_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/web_parser_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/web_parser_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/tiny/web_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/web_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
