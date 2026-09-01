# parser_multiline_shape_parity_spec

> Rust and pure-Simple parsers accept the same multiline source shapes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_multiline_shape_parity_spec

Rust and pure-Simple parsers accept the same multiline source shapes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/parser_multiline_shape_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Rust and pure-Simple parsers accept the same multiline source shapes.

## Scenarios

### bootstrap multiline parser parity

#### accepts a nested continuation that rejoins its outer chain

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a nested continuation that rejoins its outer chain
   - Expected: multiline_shape_parses(source, "rejoined_continuation") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a nested continuation that rejoins its outer chain")
val source = "fn g(x: text) -> text:\n    x\n" +
    "fn f(a: text, b: text) -> bool:\n" +
    "    a == b and\n" +
    "        a ==\n" +
    "            g(b) and\n" +
    "        a ==\n" +
    "            g(b)\n"
expect(multiline_shape_parses(source, "rejoined_continuation")).to_equal(true)
```

</details>

#### accepts consecutive trailing assignment continuations

- accepts consecutive trailing assignment continuations
   - Expected: multiline_shape_parses(source, "trailing_assignments") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts consecutive trailing assignment continuations")
val source = "struct C:\n    a: text\n    b: text\n" +
    "fn f(c: C, v: text):\n" +
    "    c.a =\n        v\n" +
    "    c.b =\n        v\n"
expect(multiline_shape_parses(source, "trailing_assignments")).to_equal(true)
```

</details>

#### accepts a return type after a trailing arrow

- accepts a return type after a trailing arrow
   - Expected: multiline_shape_parses(source, "trailing_return_arrow") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a return type after a trailing arrow")
val source = "fn f(\n" +
    "        a: text,\n" +
    "        b: text) ->\n" +
    "        Result<text, text>:\n" +
    "    Ok(a)\n"
expect(multiline_shape_parses(source, "trailing_return_arrow")).to_equal(true)
```

</details>

#### accepts inline if assignment statements

- accepts inline if assignment statements
   - Expected: multiline_shape_parses(source, "inline_if_assignment") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts inline if assignment statements")
val source = "fn f(d: {text: bool}, k: text):\n" +
    "    if k == \"t\": d[k] = true\n" +
    "    else: d[k] = false\n"
expect(multiline_shape_parses(source, "inline_if_assignment")).to_equal(true)
```

</details>

#### accepts an if expression with a multiline condition

- accepts an if expression with a multiline condition
   - Expected: multiline_shape_parses(source, "multiline_if_expression") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts an if expression with a multiline condition")
val source = "fn f(a: text, b: text) -> text:\n" +
    "    val r = if a == \"x\" and\n" +
    "            b == \"y\":\n" +
    "        a\n" +
    "    else:\n" +
    "        b\n" +
    "    r\n"
expect(multiline_shape_parses(source, "multiline_if_expression")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `7b432a969ff923a45444b26441ac750e9399d2da8f797989c71c898d13988689`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b432a969ff923a45444b26441ac750e9399d2da8f797989c71c898d13988689`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b432a969ff923a45444b26441ac750e9399d2da8f797989c71c898d13988689`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/bootstrap/parser_multiline_shape_parity_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/parser_multiline_shape_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap/parser_multiline_shape_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/parser_multiline_shape_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/parser_multiline_shape_parity_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a nested continuation that rejoins its outer chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/parser_multiline_shape_parity_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts consecutive trailing assignment continuations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/parser_multiline_shape_parity_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a return type after a trailing arrow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
