# Lexer Triple Quote Docstring Specification

> Tests covering CoreLexer triple-quoted strings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Triple Quote Docstring Specification

## Scenarios

### CoreLexer triple-quoted strings

#### joins each character slice once without immutable prefix growth

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- joins each character slice once without immutable prefix growth


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("joins each character slice once without immutable prefix growth")
val source = file_read("src/compiler/10.frontend/core/lexer_struct.spl")
val start = source.find("fn char_slice(start: i64, end: i64) -> text:")
val end = source.find("fn token_kind() -> i64:")
val body = if start >= 0 and end > start: source.substring(start, end) else: ""
expect(source).to_contain("slice_parts: [text]")
expect(source).to_contain("var core_token_text_intern: {i64: text} = {}")
# Native-codegen dict rule: interning probes with contains_key + index
# read, never `.get()`. See doc/07_guide/language/dict_native_pitfalls.md
expect(body).to_contain("core_token_text_intern.contains_key(key)")
expect(body).to_contain("val cached = core_token_text_intern[key]")
expect(body).to_contain("core_token_text_matches(self.source_chars, s, e, cached)")
expect(body).to_contain("core_token_text_intern[key] = interned")
expect(body).to_contain("self.slice_parts.clear()")
expect(body).to_contain("self.slice_parts.push(self.source_chars[i])")
expect(body).to_contain("self.slice_parts.join(\"\")")
expect(body.contains("var parts: [text] = []")).to_be(false)
expect(body.contains("result = result + self.source_chars[i]")).to_be(false)
expect(source.contains("val src: [text] = self.source_chars")).to_be(false)
expect(source).to_contain("val src_len: i64 = self.source_chars.len()")
```

</details>

#### reuses ASCII handles while preserving multibyte character slices

- reuses ASCII handles while preserving multibyte character slices


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reuses ASCII handles while preserving multibyte character slices")
val source = file_read("src/runtime/simple_core/core_string.spl")
val start = source.find("pub fn rt_string_chars(value: i64) -> i64:")
val end = source.find("pub fn rt_string_char_code_at(value: i64, index: i64) -> i64:")
val body = if start >= 0 and end > start: source.substring(start, end) else: ""
expect(body).to_contain("val ascii_cache = calloc(256, 8)")
expect(body).to_contain("if width == 1 and ascii_cache > 0:")
expect(body).to_contain("val cache_offset = b0 * 8")
expect(body).to_contain("char_value = spl_load_i64(ascii_cache, cache_offset)")
expect(body).to_contain("if string_ptr(char_value) > 0:")
expect(body).to_contain("spl_store_i64(ascii_cache, cache_offset, char_value)")
expect(body).to_contain("char_value = rt_string_new(data + byte_index, width)")
expect(body).to_contain("if ascii_cache > 0:\n        free(ascii_cache)")
```

</details>

#### keeps exact parser token text without offset reconstruction

- keeps exact parser token text without offset reconstruction
   - Expected: tokens.join("|") equals `21:val|6:LIMIT|161::|6:i64|100:=|1:128|180:|190:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps exact parser token text without offset reconstruction")
parser_init("# —\nval LIMIT: i64 = 128\n")
var tokens: [text] = []
for i in 0..16:
    tokens.push("{par_kind_get()}:" + par_text_get())
    if par_kind_get() == 190:
        break
    parser_advance()
expect(tokens.join("|")).to_equal("21:val|6:LIMIT|161::|6:i64|100:=|1:128|180:|190:")
```

</details>

#### keeps a direct integer suffix after token construction

- keeps a direct integer suffix after token construction
   - Expected: lex_next() equals `7`
   - Expected: lex_token_text() equals `0`
   - Expected: lex_cur_suffix_get() equals `u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a direct integer suffix after token construction")
lex_init("0u32")
expect(lex_next()).to_equal(7)
expect(lex_token_text()).to_equal("0")
expect(lex_cur_suffix_get()).to_equal("u32")
```

</details>

#### lexes a multi-line docstring as one string token

- lexes a multi-line docstring as one string token
   - Expected: error_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lexes a multi-line docstring as one string token")
val src = "fn f() -> i64:\n    \"\"\"line one\n    line two\n    \"\"\"\n    1\n"
lex_init(src)
var kinds: [i64] = []
var string_text = ""
var error_count = 0
for i in 0..40:
    val k = lex_next()
    if k == 0:
        break
    kinds.push(k)
    if k == 3 and string_text == "":
        string_text = lex_token_text()
    if k == 191:
        error_count = error_count + 1
# No Error tokens, and the docstring is one String token containing
# both lines.
expect(error_count).to_equal(0)
expect(string_text.contains("line one")).to_be(true)
expect(string_text.contains("line two")).to_be(true)
```

</details>

#### lexes a single-line triple-quoted string as one token

- lexes a single-line triple-quoted string as one token
   - Expected: errors equals `0`
   - Expected: found equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lexes a single-line triple-quoted string as one token")
lex_init("val x = \"\"\"abc\"\"\"\n")
var found = ""
var errors = 0
for i in 0..20:
    val k = lex_next()
    if k == 0:
        break
    if k == 3:
        found = lex_token_text()
    if k == 191:
        errors = errors + 1
expect(errors).to_equal(0)
expect(found).to_equal("abc")
```

</details>

#### keeps a long UTF-8 triple-quoted token exact through EOF

- keeps a long UTF-8 triple-quoted token exact through EOF
   - Expected: lex_next() equals `3`
   - Expected: lex_token_text() equals `payload`
   - Expected: lex_next() equals `190`
   - Expected: lex_next() equals `190`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a long UTF-8 triple-quoted token exact through EOF")
var chunks: [text] = []
for i in 0..512:
    chunks.push("abcdefgh")
val payload = chunks.join("") + "世界🚀"
lex_init("\"\"\"" + payload + "\"\"\"")
expect(lex_next()).to_equal(3)
expect(lex_token_text()).to_equal(payload)
# The stream terminates with TOK_EOF (190, tokens.spl:152), and EOF is
# sticky — every further lex_next() keeps returning it, never 0.
expect(lex_next()).to_equal(190)
expect(lex_next()).to_equal(190)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CoreLexer triple-quoted strings.
- CoreLexer triple-quoted strings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1d577207d9db6a59971d8905f47986f7c64b0d5dec90c392d7379049340fd064`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d577207d9db6a59971d8905f47986f7c64b0d5dec90c392d7379049340fd064`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d577207d9db6a59971d8905f47986f7c64b0d5dec90c392d7379049340fd064`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.spl
mirror: doc/06_spec/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins each character slice once without immutable prefix growth' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses ASCII handles while preserving multibyte character slices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps exact parser token text without offset reconstruction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
