# Parser Ce Keyword Identifier Specification

> Tests covering ce keyword identifier parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Ce Keyword Identifier Specification

## Scenarios

### ce keyword identifier parsing

#### parses ce comparisons without breaking expression-level ce blocks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses ce comparisons without breaking expression-level ce blocks
   - Expected: parser_has_errors() is false
   - Expected: decls.len() equals `7`
   - Expected: decl_get_tag(decls[0]) equals `DECL_FN`
   - Expected: decl_get_name(decls[1]) equals `builder_probe`
   - Expected: decl_get_name(decls[2]) equals `inline_chain`
   - Expected: decl_get_body(decls[2]).len() equals `2`
   - Expected: decl_get_name(decls[3]) equals `inline_val_chain`
   - Expected: decl_get_body(decls[3]).len() equals `2`
   - Expected: decl_get_name(decls[4]) equals `then_chain`
   - Expected: expr_get_tag(then_expr) equals `EXPR_IF`
   - Expected: expr_get_tag(expr_get_extra(then_expr)) equals `EXPR_IF`
   - Expected: decl_get_name(decls[5]) equals `indexed_match`
   - Expected: expr_get_tag(indexed_expr) equals `EXPR_INDEX`
   - Expected: expr_get_str(expr_get_left(indexed_expr)) equals `match`
   - Expected: stmt_get_tag(final_else[0]) equals `STMT_VAL_DECL`
   - Expected: stmt_get_name(final_else[0]) equals `ce`
   - Expected: stmt_get_tag(inner) equals `STMT_IF`
   - Expected: expr_get_tag(condition) equals `EXPR_BINARY`
   - Expected: expr_get_tag(left) equals `EXPR_IDENT`
   - Expected: expr_get_str(left) equals `ce`
   - Expected: expr_get_tag(right) equals `EXPR_INT_LIT`
   - Expected: expr_get_int(right) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 81 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses ce comparisons without breaking expression-level ce blocks")
val source = "fn classify(x: i64) -> i64:\n" +
    "    if x > 0:\n" +
    "        return 1\n" +
    "    elif x == 0:\n" +
    "        return 2\n" +
    "    else:\n" +
    "        val ce = x\n" +
    "        if ce < 0:\n" +
    "            return ce\n" +
    "        return 0\n" +
    "fn builder_probe() -> i64:\n" +
    "    val value = ce result:\n" +
    "        7\n" +
    "    value\n" +
    "fn inline_chain(basis: i64) -> i64:\n" +
    "    val value = if basis == 0: 30\n" +
    "                elif basis == 3: 31\n" +
    "                else: 32\n" +
    "    value\n" +
    "fn inline_val_chain(x: i64) -> i64:\n" +
    "    val value = if val y = x: y\n" +
    "                else: 0\n" +
    "    value\n" +
    "fn then_chain(level: i64) -> i64:\n" +
    "    val value = if level == 4 then 40 elif level == 5 then 50 else: 60\n" +
    "    value\n" +
    "fn indexed_match() -> i64:\n" +
    "    var match = [10, 20]\n" +
    "    val first = match[0]\n" +
    "    match[0] = 30\n" +
    "    match [first]:\n" +
    "        _:\n" +
    "            return first\n" +
    "fn grouped_arm(name: text) -> i64:\n" +
    "    match name:\n" +
    "        \"A\", \"B\":\n" +
    "            return 1\n" +
    "        case \"C\", \"D\":\n" +
    "            return 2\n" +
    "        _:\n" +
    "            return 0\n"

ast_reset()
parse_module(source, "parser_ce_keyword_identifier_spec.spl")
expect(parser_has_errors()).to_equal(false)

val decls = module_get_decls()
expect(decls.len()).to_equal(7)
expect(decl_get_tag(decls[0])).to_equal(DECL_FN)
expect(decl_get_name(decls[1])).to_equal("builder_probe")
expect(decl_get_name(decls[2])).to_equal("inline_chain")
expect(decl_get_body(decls[2]).len()).to_equal(2)
expect(decl_get_name(decls[3])).to_equal("inline_val_chain")
expect(decl_get_body(decls[3]).len()).to_equal(2)
expect(decl_get_name(decls[4])).to_equal("then_chain")
val then_expr = stmt_get_expr(decl_get_body(decls[4])[0])
expect(expr_get_tag(then_expr)).to_equal(EXPR_IF)
expect(expr_get_tag(expr_get_extra(then_expr))).to_equal(EXPR_IF)
expect(decl_get_name(decls[5])).to_equal("indexed_match")
val indexed_expr = stmt_get_expr(decl_get_body(decls[5])[1])
expect(expr_get_tag(indexed_expr)).to_equal(EXPR_INDEX)
expect(expr_get_str(expr_get_left(indexed_expr))).to_equal("match")

val outer = decl_get_body(decls[0])[0]
val elif_stmt = elif_get_else(stmt_get_type(outer))[0]
val final_else = elif_get_else(stmt_get_type(elif_stmt))
expect(stmt_get_tag(final_else[0])).to_equal(STMT_VAL_DECL)
expect(stmt_get_name(final_else[0])).to_equal("ce")

val inner = final_else[1]
expect(stmt_get_tag(inner)).to_equal(STMT_IF)
val condition = stmt_get_expr(inner)
expect(expr_get_tag(condition)).to_equal(EXPR_BINARY)
val left = expr_get_left(condition)
val right = expr_get_right(condition)
expect(expr_get_tag(left)).to_equal(EXPR_IDENT)
expect(expr_get_str(left)).to_equal("ce")
expect(expr_get_tag(right)).to_equal(EXPR_INT_LIT)
expect(expr_get_int(right)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/core/parser_ce_keyword_identifier_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ce keyword identifier parsing.
- ce keyword identifier parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `83674ebd8858dcc3cfec66900252562ebfadabecbc7638b4e7613c13bb603279`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `83674ebd8858dcc3cfec66900252562ebfadabecbc7638b4e7613c13bb603279`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `83674ebd8858dcc3cfec66900252562ebfadabecbc7638b4e7613c13bb603279`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/core/parser_ce_keyword_identifier_spec.spl
mirror: doc/06_spec/01_unit/core/parser_ce_keyword_identifier_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/core/parser_ce_keyword_identifier_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/core/parser_ce_keyword_identifier_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/core/parser_ce_keyword_identifier_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/core/parser_ce_keyword_identifier_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses ce comparisons without breaking expression-level ce blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
