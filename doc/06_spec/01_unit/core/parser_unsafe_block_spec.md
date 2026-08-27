# Parser Unsafe Block Specification

> Tests covering unsafe/danger block parsing (self-hosted).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Unsafe Block Specification

## Scenarios

### unsafe/danger block parsing (self-hosted)

#### parses unsafe: and danger: blocks into EXPR_UNSAFE_BLOCK

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- execute scenario
   - Expected: parser_has_errors() is false
   - Expected: decls.len() equals `1`
   - Expected: decl_get_tag(decls[0]) equals `DECL_FN`
   - Expected: decl_get_name(decls[0]) equals `poke`
   - Expected: body.len() equals `3`
   - Expected: expr_get_tag(unsafe_expr) equals `EXPR_UNSAFE_BLOCK`
   - Expected: expr_get_stmts(unsafe_expr).len() equals `2`
   - Expected: expr_get_tag(danger_expr) equals `EXPR_UNSAFE_BLOCK`
   - Expected: expr_get_stmts(danger_expr).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PARSER-UNSAFE
step("execute scenario")
val source = "fn poke() -> i64:\n" +
    "    unsafe:\n" +
    "        val a = 1\n" +
    "        val b = 2\n" +
    "    danger:\n" +
    "        val c = 3\n" +
    "    7\n"

ast_reset()
parse_module(source, "parser_unsafe_block_spec.spl")
expect(parser_has_errors()).to_equal(false)

val decls = module_get_decls()
expect(decls.len()).to_equal(1)
expect(decl_get_tag(decls[0])).to_equal(DECL_FN)
expect(decl_get_name(decls[0])).to_equal("poke")

val body = decl_get_body(decls[0])
# unsafe: block, danger: block, trailing return expr
expect(body.len()).to_equal(3)

val unsafe_expr = stmt_get_expr(body[0])
expect(expr_get_tag(unsafe_expr)).to_equal(EXPR_UNSAFE_BLOCK)
expect(expr_get_stmts(unsafe_expr).len()).to_equal(2)

val danger_expr = stmt_get_expr(body[1])
expect(expr_get_tag(danger_expr)).to_equal(EXPR_UNSAFE_BLOCK)
expect(expr_get_stmts(danger_expr).len()).to_equal(1)
```

</details>

#### leaves plain unsafe/danger identifiers untouched

- execute scenario
   - Expected: parser_has_errors() is false
   - Expected: decls.len() equals `1`
   - Expected: body.len() equals `4`
   - Expected: ub_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PARSER-UNSAFE
step("execute scenario")
val source = "fn ident_uses() -> i64:\n" +
    "    var unsafe = 5\n" +
    "    unsafe = 7\n" +
    "    val danger = unsafe + 1\n" +
    "    danger\n"

ast_reset()
parse_module(source, "parser_unsafe_block_spec.spl")
expect(parser_has_errors()).to_equal(false)

val decls = module_get_decls()
expect(decls.len()).to_equal(1)
val body = decl_get_body(decls[0])
expect(body.len()).to_equal(4)
# No statement became an unsafe block
var ub_count = 0
var si = 0
while si < body.len():
    val e = stmt_get_expr(body[si])
    if e >= 0 and expr_get_tag(e) == EXPR_UNSAFE_BLOCK:
        ub_count = ub_count + 1
    si = si + 1
expect(ub_count).to_equal(0)
```

</details>

#### records @unsafe(reason, capabilities) fn annotation metadata

- execute scenario
   - Expected: parser_has_errors() is false
   - Expected: annos.len() equals `1`
   - Expected: annos[0] equals `poke_mmio|mmio poke|raw_ptr,mmio`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PARSER-UNSAFE
step("execute scenario")
val source = "@unsafe(reason: \"mmio poke\", capabilities: [raw_ptr, mmio])\n" +
    "fn poke_mmio() -> i64:\n" +
    "    2\n"

ast_reset()
parse_module(source, "parser_unsafe_block_spec.spl")
expect(parser_has_errors()).to_equal(false)

val annos = parser_unsafe_annotations_get()
expect(annos.len()).to_equal(1)
expect(annos[0]).to_equal("poke_mmio|mmio poke|raw_ptr,mmio")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/core/parser_unsafe_block_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering unsafe/danger block parsing (self-hosted).
- unsafe/danger block parsing (self-hosted)

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
- `REQ-SSPEC-PARSER-UNSAFE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `11ef1ef5d1df646c376ffc404e1f7209a8b9dfbbae50b7eeda490387b3e21d5d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11ef1ef5d1df646c376ffc404e1f7209a8b9dfbbae50b7eeda490387b3e21d5d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11ef1ef5d1df646c376ffc404e1f7209a8b9dfbbae50b7eeda490387b3e21d5d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/core/parser_unsafe_block_spec.spl
mirror: doc/06_spec/01_unit/core/parser_unsafe_block_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/core/parser_unsafe_block_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/core/parser_unsafe_block_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/core/parser_unsafe_block_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/core/parser_unsafe_block_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/core/parser_unsafe_block_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses unsafe: and danger: blocks into EXPR_UNSAFE_BLOCK' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/core/parser_unsafe_block_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves plain unsafe/danger identifiers untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/core/parser_unsafe_block_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records @unsafe(reason, capabilities) fn annotation metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
