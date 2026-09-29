# `literal` as an ordinary identifier

> `literal` introduces a literal-suffix function declaration — `literal fn _re(...)`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `literal` as an ordinary identifier

`literal` introduces a literal-suffix function declaration — `literal fn _re(...)`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language / Parser |
| Status | Regression guard (reproducing spec) |
| Source | `test/01_unit/compiler/parser_literal_soft_keyword_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`literal` introduces a literal-suffix function declaration — `literal fn _re(...)`
— and nothing else. It is also an entirely reasonable variable name: a token's
literal text, a parsed literal node, a config literal.

The seed lexer maps the bare word to `TokenKind::Literal` unconditionally
(`parser/src/lexer/identifiers.rs:254`), and *expression* position already coped
with that via `parse_keyword_identifier("literal")`. **Statement** position did
not: `parse_statement` routed `TokenKind::Literal` straight into
`parse_literal_function`, whose first act is `expect(&TokenKind::Fn)`. So a
statement as ordinary as

    literal = 2

died with

    parse: Unexpected token: expected Fn, found Assign

a diagnostic that names an unrelated token and never mentions that `literal` is a
keyword — the reader has no way to reach the real cause from it.

The audience is anyone touching the statement-start dispatch in
`parser_impl/core.rs`. The fix mirrors the `from` disambiguation already sitting a
few lines below it: route to the declaration parser only when the next token is
`Fn`, otherwise fall through to `parse_expression_or_assignment`.

## Scope and Preconditions

Requires a seed built at or after 2026-08-17. On an older binary this file fails
to LOAD with the `expected Fn, found Assign` error above — that load failure is
the reproduction.

## Primary Workflow

Declare a variable named `literal`, then reassign it — the statement position that
used to fail — and read it back in the ordinary expression positions.

See doc/08_tracking/bug/seed_lexer_literal_soft_keyword_shadows_identifier_2026-07-30.md

## Scenarios

### literal as an ordinary identifier

#### reassigns a variable named literal in statement position

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reassigns a variable named literal in statement position
- Declare it -- the declaration form was already accepted
- Reassign it as a bare statement: the shape that reported `expected Fn, found Assign`
   - Expected: literal equals `2`
- Compound reassignment goes through the same statement dispatch
   - Expected: literal equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reassigns a variable named literal in statement position")
step("Declare it -- the declaration form was already accepted")
var literal = 1

step("Reassign it as a bare statement: the shape that reported `expected Fn, found Assign`")
literal = 2
expect(literal).to_equal(2)

step("Compound reassignment goes through the same statement dispatch")
literal = literal + 40
expect(literal).to_equal(42)
```

</details>

#### reads a variable named literal in expression positions

- reads a variable named literal in expression positions
- Expression position already worked; assert it still does after the fix
   - Expected: literal + 1 equals `8`
   - Expected: 3 + literal equals `10`
- As a function argument and as an index
   - Expected: xs[idx] equals `20`
   - Expected: str(literal) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads a variable named literal in expression positions")
step("Expression position already worked; assert it still does after the fix")
var literal = 7
expect(literal + 1).to_equal(8)
expect(3 + literal).to_equal(10)

step("As a function argument and as an index")
val xs = [10, 20, 30]
var idx = 1
expect(xs[idx]).to_equal(20)
expect(str(literal)).to_equal("7")
```

</details>

#### uses literal as a text-valued name, the way a lexer would

- uses literal as a text-valued name, the way a lexer would
- The motivating real-world use: a token's literal text
   - Expected: literal equals `abcd`
   - Expected: literal.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses literal as a text-valued name, the way a lexer would")
step("The motivating real-world use: a token's literal text")
var literal = "abc"
literal = literal + "d"
expect(literal).to_equal("abcd")
expect(literal.len()).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-PARSER-CONTEXTUAL-LITERAL-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `70a12e139d133ffa7ed6df9260df656f7280ef97bbaa38e00957c1c5ae999977`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70a12e139d133ffa7ed6df9260df656f7280ef97bbaa38e00957c1c5ae999977`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70a12e139d133ffa7ed6df9260df656f7280ef97bbaa38e00957c1c5ae999977`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/parser_literal_soft_keyword_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_literal_soft_keyword_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/parser_literal_soft_keyword_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_literal_soft_keyword_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_literal_soft_keyword_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser_literal_soft_keyword_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/parser_literal_soft_keyword_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reassigns a variable named literal in statement position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_literal_soft_keyword_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a variable named literal in expression positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_literal_soft_keyword_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses literal as a text-valued name, the way a lexer would' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
