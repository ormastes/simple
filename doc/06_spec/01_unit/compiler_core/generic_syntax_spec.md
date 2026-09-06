# Generic Syntax Specification

> Tests covering Generic Syntax.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Syntax Specification

## Scenarios

### Generic Syntax

#### should parse generic type parameter lists on declarations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should parse generic type parameter lists on declarations
   - Expected: src contains `fn parse_type_params() -> [text]`
   - Expected: src contains `val has_lt: bool = par_kind_get() == 82`
   - Expected: src contains `val has_lt_gen: bool = par_kind_get() == 86`
   - Expected: src contains `type_params.push(param_name)`
   - Expected: src contains `parser_expect(83)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should parse generic type parameter lists on declarations")
val src = read_source("src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl")
expect(src.contains("fn parse_type_params() -> [text]")).to_equal(true)
expect(src.contains("val has_lt: bool = par_kind_get() == 82")).to_equal(true)
expect(src.contains("val has_lt_gen: bool = par_kind_get() == 86")).to_equal(true)
expect(src.contains("type_params.push(param_name)")).to_equal(true)
expect(src.contains("parser_expect(83)")).to_equal(true)
```

</details>

#### should support inline generic constraints

- should support inline generic constraints
   - Expected: src contains `parse_type_param_constraint_list`
   - Expected: src contains `val is_limits: bool = par_kind_get() == 214`
   - Expected: src contains `val is_candidates: bool = par_kind_get() == 215`
   - Expected: src contains `file_generic_constraints[param_name] = filtered`
   - Expected: src contains `file_generic_constraint_modes[param_name] = mode_str`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should support inline generic constraints")
val src = read_source("src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl")
expect(src.contains("parse_type_param_constraint_list")).to_equal(true)
expect(src.contains("val is_limits: bool = par_kind_get() == 214")).to_equal(true)
expect(src.contains("val is_candidates: bool = par_kind_get() == 215")).to_equal(true)
expect(src.contains("file_generic_constraints[param_name] = filtered")).to_equal(true)
expect(src.contains("file_generic_constraint_modes[param_name] = mode_str")).to_equal(true)
```

</details>

#### should attach generic parameters to function declarations

- should attach generic parameters to function declarations
   - Expected: src contains `val type_params = parse_type_params()`
   - Expected: src contains `decl_fn(fn_name, param_names, param_types, ret_type, body, is_async, type_par... (full value in folded executable source)`
   - Expected: src contains `decl_extern_fn(fn_name, param_names, param_types, ret_type, type_params, decl... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should attach generic parameters to function declarations")
val src = read_source("src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl")
expect(src.contains("val type_params = parse_type_params()")).to_equal(true)
# STALE-SPEC REPOINT (2026-08-10): these two needles ended in a hardcoded
# `, 0)` span argument and had been RED since the parser started
# propagating a real span (`decl_span`) instead. The capability under
# test — `type_params` reaching both declaration constructors — is
# intact; only the trailing span argument changed. Anchored on the
# type_params tail so a future span change cannot re-break this, while a
# dropped type_params still fails.
expect(src.contains("decl_fn(fn_name, param_names, param_types, ret_type, body, is_async, type_params, decl_span)")).to_equal(true)
expect(src.contains("decl_extern_fn(fn_name, param_names, param_types, ret_type, type_params, decl_span)")).to_equal(true)
```

</details>

#### should persist generic parameters in AST declarations

- should persist generic parameters in AST declarations
   - Expected: src contains `var decl_type_params: [[text]] = []`
   - Expected: src contains `fn decl_fn(name: text, param_names: [text], param_types: [i64], ret_type: i64... (full value in folded executable source)`
   - Expected: src contains `ast_decl_text_set(idx, "TYPE_PARAMS", ast_text_list_join(type_params))`
   - Expected: src contains `fn decl_get_type_params(idx: i64) -> [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should persist generic parameters in AST declarations")
val src = read_source("src/compiler/10.frontend/core/_Ast/decl_nodes.spl")
expect(src.contains("var decl_type_params: [[text]] = []")).to_equal(true)
expect(src.contains("fn decl_fn(name: text, param_names: [text], param_types: [i64], ret_type: i64, body: [i64], is_async: i64, type_params: [text], span_id: i64) -> i64")).to_equal(true)
expect(src.contains("ast_decl_text_set(idx, \"TYPE_PARAMS\", ast_text_list_join(type_params))")).to_equal(true)
expect(src.contains("fn decl_get_type_params(idx: i64) -> [text]")).to_equal(true)
```

</details>

#### should parse generic type annotations without confusing comparisons

- should parse generic type annotations without confusing comparisons
   - Expected: src contains `val has_lt_gen: bool = kind == TOK_LT_GENERIC`
   - Expected: src contains `val has_generic: bool = has_lt or has_lt_gen`
   - Expected: src contains `if type_name == "Option"`
   - Expected: src contains `if type_name == "Result"`
   - Expected: src contains `if type_name == "Dict"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should parse generic type annotations without confusing comparisons")
val src = read_source("src/compiler/10.frontend/core/parser.spl")
# Anchored to real parser code; the "# Check for generic type: Option<T>,
# ..." comment must not be able to satisfy this.
expect(src.contains("val has_lt_gen: bool = kind == TOK_LT_GENERIC")).to_equal(true)
expect(src.contains("val has_generic: bool = has_lt or has_lt_gen")).to_equal(true)
expect(src.contains("if type_name == \"Option\"")).to_equal(true)
expect(src.contains("if type_name == \"Result\"")).to_equal(true)
expect(src.contains("if type_name == \"Dict\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/generic_syntax_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Generic Syntax.
- Generic Syntax

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

- Canonical SPipe generation for source `a3798b715732fabdc65645ef8490d3760789cd98d9b741b0442faa030298c331`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3798b715732fabdc65645ef8490d3760789cd98d9b741b0442faa030298c331`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3798b715732fabdc65645ef8490d3760789cd98d9b741b0442faa030298c331`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler_core/generic_syntax_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/generic_syntax_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/generic_syntax_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/generic_syntax_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/generic_syntax_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse generic type parameter lists on declarations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/generic_syntax_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse generic type parameter lists on declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/generic_syntax_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should support inline generic constraints' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/generic_syntax_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should support inline generic constraints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/generic_syntax_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should attach generic parameters to function declarations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/generic_syntax_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should attach generic parameters to function declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/generic_syntax_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should persist generic parameters in AST declarations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/generic_syntax_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse generic type annotations without confusing comparisons' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
