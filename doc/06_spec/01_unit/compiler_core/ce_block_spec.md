# Ce Block Specification

> Tests covering Ce Block.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ce Block Specification

## Scenarios

### Ce Block

#### should reserve declaration and token tags for ce blocks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reserve declaration and token tags for ce blocks
   - Expected: ast_src contains `const DECL_CE = 11`
   - Expected: token_src contains `const TOK_KW_CE: i64 = 205`
   - Expected: token_src contains `if name == "ce": return TOK_KW_CE`
   - Expected: token_src contains `if kind == TOK_KW_CE: return "ce"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should reserve declaration and token tags for ce blocks")
val ast_src = read_source("src/compiler/10.frontend/core/_Ast/decl_nodes.spl")
val token_src = read_source("src/compiler/10.frontend/core/tokens.spl")
expect(ast_src.contains("const DECL_CE = 11")).to_equal(true)
expect(token_src.contains("const TOK_KW_CE: i64 = 205")).to_equal(true)
expect(token_src.contains("if name == \"ce\": return TOK_KW_CE")).to_equal(true)
expect(token_src.contains("if kind == TOK_KW_CE: return \"ce\"")).to_equal(true)
```

</details>

#### should construct ce declarations with builder name and body

- should construct ce declarations with builder name and body
   - Expected: ast_src contains `fn decl_ce_block(builder_name: text, body_stmts: [i64], span_id: i64) -> i64`
   - Expected: ast_src contains `val idx = decl_alloc(DECL_CE, span_id)`
   - Expected: ast_src contains `decl_name[idx] = builder_name`
   - Expected: ast_src contains `decl_body_stmts[idx] = body_stmts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should construct ce declarations with builder name and body")
val ast_src = read_source("src/compiler/10.frontend/core/_Ast/decl_nodes.spl")
expect(ast_src.contains("fn decl_ce_block(builder_name: text, body_stmts: [i64], span_id: i64) -> i64")).to_equal(true)
expect(ast_src.contains("val idx = decl_alloc(DECL_CE, span_id)")).to_equal(true)
expect(ast_src.contains("decl_name[idx] = builder_name")).to_equal(true)
expect(ast_src.contains("decl_body_stmts[idx] = body_stmts")).to_equal(true)
```

</details>

#### should expose ce declarations through parser and core exports

- should expose ce declarations through parser and core exports
   - Expected: parser_src contains `use compiler.core.ast.{DECL_CE, decl_ce_block}`
   - Expected: parser_src contains `TOK_KW_CE`
   - Expected: init_src contains `export DECL_CE, decl_ce_block`
   - Expected: init_src contains `export TOK_KW_BIND, TOK_KW_CE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose ce declarations through parser and core exports")
val parser_src = read_source("src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl")
val init_src = read_source("src/compiler/10.frontend/core/__init__.spl")
expect(parser_src.contains("use compiler.core.ast.{DECL_CE, decl_ce_block}")).to_equal(true)
expect(parser_src.contains("TOK_KW_CE")).to_equal(true)
expect(init_src.contains("export DECL_CE, decl_ce_block")).to_equal(true)
expect(init_src.contains("export TOK_KW_BIND, TOK_KW_CE")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/ce_block_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Ce Block.
- Ce Block

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

- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2fa1ff2d11c790c22e70420cba78ff10014021e94191b53e01ae9f80857020f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2fa1ff2d11c790c22e70420cba78ff10014021e94191b53e01ae9f80857020f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2fa1ff2d11c790c22e70420cba78ff10014021e94191b53e01ae9f80857020f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler_core/ce_block_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/ce_block_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/ce_block_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/ce_block_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/ce_block_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reserve declaration and token tags for ce blocks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/ce_block_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reserve declaration and token tags for ce blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/ce_block_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct ce declarations with builder name and body' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/ce_block_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should construct ce declarations with builder name and body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/ce_block_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose ce declarations through parser and core exports' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/ce_block_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose ce declarations through parser and core exports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
