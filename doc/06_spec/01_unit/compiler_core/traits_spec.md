# Traits Specification

> Tests covering Traits.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Specification

## Scenarios

### Traits

#### should reserve tokens for keyof and static_for

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reserve tokens for keyof and static_for
   - Expected: src contains `const TOK_KW_KEYOF: i64 = 200`
   - Expected: src contains `const TOK_KW_STATIC_FOR: i64 = 201`
   - Expected: src contains `if name == "keyof": return TOK_KW_KEYOF`
   - Expected: src contains `if name == "static_for": return TOK_KW_STATIC_FOR`
   - Expected: src contains `if kind == TOK_KW_KEYOF: return "keyof"`
   - Expected: src contains `if kind == TOK_KW_STATIC_FOR: return "static_for"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should reserve tokens for keyof and static_for")
val src = read_source("src/compiler/10.frontend/core/tokens.spl")
expect(src.contains("const TOK_KW_KEYOF: i64 = 200")).to_equal(true)
expect(src.contains("const TOK_KW_STATIC_FOR: i64 = 201")).to_equal(true)
expect(src.contains("if name == \"keyof\": return TOK_KW_KEYOF")).to_equal(true)
expect(src.contains("if name == \"static_for\": return TOK_KW_STATIC_FOR")).to_equal(true)
expect(src.contains("if kind == TOK_KW_KEYOF: return \"keyof\"")).to_equal(true)
expect(src.contains("if kind == TOK_KW_STATIC_FOR: return \"static_for\"")).to_equal(true)
```

</details>

#### should desugar annotation calls and keyof into traits calls

- should desugar annotation calls and keyof into traits calls
   - Expected: src contains `at_args.push(expr_string_lit(ann_name, 0))`
   - Expected: src contains `val at_callee = expr_ident("__traits", 0)`
   - Expected: src contains `val at_builtin_name = "__builtin_" + ann_name`
   - Expected: src contains `keyof_args.push(expr_string_lit("fields", 0))`
   - Expected: src contains `val keyof_callee = expr_ident("__traits", 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should desugar annotation calls and keyof into traits calls")
val src = read_source("src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl")
# Anchored to real desugar code; the "# @traits(query, T, ...) desugars
# to __traits" comment must not be able to satisfy this.
expect(src.contains("at_args.push(expr_string_lit(ann_name, 0))")).to_equal(true)
expect(src.contains("val at_callee = expr_ident(\"__traits\", 0)")).to_equal(true)
expect(src.contains("val at_builtin_name = \"__builtin_\" + ann_name")).to_equal(true)
expect(src.contains("keyof_args.push(expr_string_lit(\"fields\", 0))")).to_equal(true)
expect(src.contains("val keyof_callee = expr_ident(\"__traits\", 0)")).to_equal(true)
```

</details>

#### should parse and build static_for statements

- should parse and build static_for statements
   - Expected: parser_src contains `fn parse_static_for_stmt() -> i64`
   - Expected: parser_src contains `stmt_static_for_stmt(iter_name, iterable, body, 0)`
   - Expected: ast_src contains `const STMT_STATIC_FOR = 17`
   - Expected: ast_src contains `fn stmt_static_for_stmt(iter_name: text, iterable: i64, body_stmts: [i64], sp... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should parse and build static_for statements")
val parser_src = read_source("src/compiler/10.frontend/core/parser_stmts.spl")
val ast_src = read_source("src/compiler/10.frontend/core/ast_stmt.spl")
expect(parser_src.contains("fn parse_static_for_stmt() -> i64")).to_equal(true)
expect(parser_src.contains("stmt_static_for_stmt(iter_name, iterable, body, 0)")).to_equal(true)
expect(ast_src.contains("const STMT_STATIC_FOR = 17")).to_equal(true)
expect(ast_src.contains("fn stmt_static_for_stmt(iter_name: text, iterable: i64, body_stmts: [i64], span_id: i64) -> i64")).to_equal(true)
```

</details>

#### should evaluate core traits reflection queries

- should evaluate core traits reflection queries
   - Expected: src contains `if name == "__traits"`
   - Expected: src contains `if tr_query == "fields"`
   - Expected: src contains `if tr_query == "has_member"`
   - Expected: src contains `if tr_query == "enum_members"`
   - Expected: src contains `if tr_query == "is_struct"`
   - Expected: src contains `if tr_query == "is_enum"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should evaluate core traits reflection queries")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("if name == \"__traits\"")).to_equal(true)
expect(src.contains("if tr_query == \"fields\"")).to_equal(true)
expect(src.contains("if tr_query == \"has_member\"")).to_equal(true)
expect(src.contains("if tr_query == \"enum_members\"")).to_equal(true)
expect(src.contains("if tr_query == \"is_struct\"")).to_equal(true)
expect(src.contains("if tr_query == \"is_enum\"")).to_equal(true)
```

</details>

<details>
<summary>Advanced: should execute static_for using normal loop semantics in interpreter mode</summary>

#### should execute static_for using normal loop semantics in interpreter mode

- should execute static_for using normal loop semantics in interpreter mode
   - Expected: src contains `fn eval_stmt_static_for(sid: i64) -> i64`
   - Expected: src contains `val sf_iterable_array = val_iterable_array(sf_iterable)`
   - Expected: src contains `env_define(sf_iter_name, sf_elem_vid)`
   - Expected: src contains `eval_set_error("static_for: cannot iterate over "`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should execute static_for using normal loop semantics in interpreter mode")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("fn eval_stmt_static_for(sid: i64) -> i64")).to_equal(true)
expect(src.contains("val sf_iterable_array = val_iterable_array(sf_iterable)")).to_equal(true)
expect(src.contains("env_define(sf_iter_name, sf_elem_vid)")).to_equal(true)
expect(src.contains("eval_set_error(\"static_for: cannot iterate over \"")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/traits_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Traits.
- Traits

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

- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `54b808d882826c6fd296005c452d105e036a9e3a5ce44ec95355da65d31a0d09`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `54b808d882826c6fd296005c452d105e036a9e3a5ce44ec95355da65d31a0d09`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `54b808d882826c6fd296005c452d105e036a9e3a5ce44ec95355da65d31a0d09`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler_core/traits_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/traits_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/traits_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/traits_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/traits_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reserve tokens for keyof and static_for' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reserve tokens for keyof and static_for' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should desugar annotation calls and keyof into traits calls' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should desugar annotation calls and keyof into traits calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse and build static_for statements' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse and build static_for statements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should evaluate core traits reflection queries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute static_for using normal loop semantics in interpreter mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
