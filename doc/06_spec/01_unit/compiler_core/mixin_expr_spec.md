# Mixin Expr Specification

> Tests covering Mixin Expr.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mixin Expr Specification

## Scenarios

### Mixin Expr

#### should reserve the mixin keyword token

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reserve the mixin keyword token
   - Expected: src contains `const TOK_KW_MIXIN: i64 = 203`
   - Expected: src contains `if name == "mixin": return TOK_KW_MIXIN`
   - Expected: src contains `if kind == TOK_KW_MIXIN: return "mixin"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should reserve the mixin keyword token")
val src = read_source("src/compiler/10.frontend/core/tokens.spl")
expect(src.contains("const TOK_KW_MIXIN: i64 = 203")).to_equal(true)
expect(src.contains("if name == \"mixin\": return TOK_KW_MIXIN")).to_equal(true)
expect(src.contains("if kind == TOK_KW_MIXIN: return \"mixin\"")).to_equal(true)
```

</details>

#### should parse mixin calls as __mixin builtin calls

- should parse mixin calls as __mixin builtin calls
   - Expected: src contains `if par_kind_get() == 203:`
   - Expected: src contains `var mixin_args_list: [i64] = []`
   - Expected: src contains `val mixin_arg = parse_expr()`
   - Expected: src contains `val mixin_callee = expr_ident("__mixin", 0)`
   - Expected: src contains `return expr_call(mixin_callee, mixin_args_list, 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should parse mixin calls as __mixin builtin calls")
val src = read_source("src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl")
# Anchored to real parser code; the "# mixin(code_text) -- compile-time
# code generation" comment must not be able to satisfy this.
expect(src.contains("if par_kind_get() == 203:")).to_equal(true)
expect(src.contains("var mixin_args_list: [i64] = []")).to_equal(true)
expect(src.contains("val mixin_arg = parse_expr()")).to_equal(true)
expect(src.contains("val mixin_callee = expr_ident(\"__mixin\", 0)")).to_equal(true)
expect(src.contains("return expr_call(mixin_callee, mixin_args_list, 0)")).to_equal(true)
```

</details>

#### should evaluate mixin code by parsing generated source

- should evaluate mixin code by parsing generated source
   - Expected: src contains `if name == "__mixin"`
   - Expected: src contains `val mx_code = val_to_text(mx_code_val)`
   - Expected: src contains `parse_module_file(mx_code, "mixin_generated.spl")`
   - Expected: src contains `val mx_all_decls = module_get_decls()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should evaluate mixin code by parsing generated source")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("if name == \"__mixin\"")).to_equal(true)
expect(src.contains("val mx_code = val_to_text(mx_code_val)")).to_equal(true)
expect(src.contains("parse_module_file(mx_code, \"mixin_generated.spl\")")).to_equal(true)
expect(src.contains("val mx_all_decls = module_get_decls()")).to_equal(true)
```

</details>

#### should register generated functions structs and declarations

- should register generated functions structs and declarations
   - Expected: src contains `func_table_register(mx_fn_name, mx_did)`
   - Expected: src contains `func_register_return_type(mx_fn_name, decl_get(mx_did).ret_type)`
   - Expected: src contains `struct_table_register(mx_struct_name, mx_did)`
   - Expected: src contains `eval_decl(mx_did2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should register generated functions structs and declarations")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("func_table_register(mx_fn_name, mx_did)")).to_equal(true)
expect(src.contains("func_register_return_type(mx_fn_name, decl_get(mx_did).ret_type)")).to_equal(true)
expect(src.contains("struct_table_register(mx_struct_name, mx_did)")).to_equal(true)
expect(src.contains("eval_decl(mx_did2)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/mixin_expr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mixin Expr.
- Mixin Expr

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `3de24f53af17a3994527919a2a01d54e8840a24cf66019e0ae462b7d89cf1d50`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3de24f53af17a3994527919a2a01d54e8840a24cf66019e0ae462b7d89cf1d50`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3de24f53af17a3994527919a2a01d54e8840a24cf66019e0ae462b7d89cf1d50`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler_core/mixin_expr_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/mixin_expr_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/mixin_expr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/mixin_expr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/mixin_expr_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reserve the mixin keyword token' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/mixin_expr_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reserve the mixin keyword token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/mixin_expr_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse mixin calls as __mixin builtin calls' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/mixin_expr_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse mixin calls as __mixin builtin calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/mixin_expr_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should evaluate mixin code by parsing generated source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/mixin_expr_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should evaluate mixin code by parsing generated source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/mixin_expr_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should register generated functions structs and declarations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
