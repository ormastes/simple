# File Class Introspection Specification

> Tests covering File Class Introspection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Class Introspection Specification

## Scenarios

### File Class Introspection

#### should desugar dotted FILE access into module_file traits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should desugar dotted FILE access into module_file traits
   - Expected: src contains `ppo_mf_args.push(expr_string_lit("module_file", 0))`
   - Expected: src contains `pp_mf_args.push(expr_string_lit("module_file", 0))`
   - Expected: src contains `val ppo_mf_callee = expr_ident("__traits", 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should desugar dotted FILE access into module_file traits")
val src = read_source("src/compiler/10.frontend/core/parser_expr.spl")
# Anchored to real code at BOTH postfix dispatch sites; the
# "# --- .FILE -> __traits(...)" banner comments must not satisfy these.
expect(src.contains("ppo_mf_args.push(expr_string_lit(\"module_file\", 0))")).to_equal(true)
expect(src.contains("pp_mf_args.push(expr_string_lit(\"module_file\", 0))")).to_equal(true)
expect(src.contains("val ppo_mf_callee = expr_ident(\"__traits\", 0)")).to_equal(true)
```

</details>

#### should desugar class and wildcard access into traits calls

- should desugar class and wildcard access into traits calls
   - Expected: src contains `ppo_ci_args.push(expr_string_lit("class_info", 0))`
   - Expected: src contains `pp_ci_args.push(expr_string_lit("class_info", 0))`
   - Expected: src contains `ppo_mw_args.push(expr_string_lit("module_wildcard", 0))`
   - Expected: src contains `pp_mw_args.push(expr_string_lit("module_wildcard", 0))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should desugar class and wildcard access into traits calls")
val src = read_source("src/compiler/10.frontend/core/parser_expr.spl")
# Anchored to real code at BOTH postfix dispatch sites; the
# "# --- .class -> ..." / "# --- .* -> ..." banner comments must not
# satisfy these.
expect(src.contains("ppo_ci_args.push(expr_string_lit(\"class_info\", 0))")).to_equal(true)
expect(src.contains("pp_ci_args.push(expr_string_lit(\"class_info\", 0))")).to_equal(true)
expect(src.contains("ppo_mw_args.push(expr_string_lit(\"module_wildcard\", 0))")).to_equal(true)
expect(src.contains("pp_mw_args.push(expr_string_lit(\"module_wildcard\", 0))")).to_equal(true)
```

</details>

#### should return File structs for module_file queries

- should return File structs for module_file queries
   - Expected: src contains `if tr_query == "module_file"`
   - Expected: src contains `val mf_file_path = module_get_file_path(mf_mod_name)`
   - Expected: src contains `var mf_fields: [text] = ["path", "module_name", "exists"]`
   - Expected: src contains `return val_make_struct("File", mf_fields, mf_vals)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return File structs for module_file queries")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("if tr_query == \"module_file\"")).to_equal(true)
expect(src.contains("val mf_file_path = module_get_file_path(mf_mod_name)")).to_equal(true)
expect(src.contains("var mf_fields: [text] = [\"path\", \"module_name\", \"exists\"]")).to_equal(true)
expect(src.contains("return val_make_struct(\"File\", mf_fields, mf_vals)")).to_equal(true)
```

</details>

#### should return Class structs with fields methods and counts

- should return Class structs with fields methods and counts
   - Expected: src contains `if tr_query == "class_info"`
   - Expected: src contains `val ci_struct_decl = struct_table_lookup(ci_type_name)`
   - Expected: src contains `"field_count", "method_count"`
   - Expected: src contains `ci_s_vals.push(val_make_int(ci_field_names.len()))`
   - Expected: src contains `return val_make_struct("Class", ci_s_fields, ci_s_vals)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return Class structs with fields methods and counts")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("if tr_query == \"class_info\"")).to_equal(true)
expect(src.contains("val ci_struct_decl = struct_table_lookup(ci_type_name)")).to_equal(true)
expect(src.contains("\"field_count\", \"method_count\"")).to_equal(true)
expect(src.contains("ci_s_vals.push(val_make_int(ci_field_names.len()))")).to_equal(true)
expect(src.contains("return val_make_struct(\"Class\", ci_s_fields, ci_s_vals)")).to_equal(true)
```

</details>

#### should return File arrays for module wildcard queries

- should return File arrays for module wildcard queries
   - Expected: src contains `if tr_query == "module_wildcard"`
   - Expected: src contains `val mw_prefix = val_to_text(mw_prefix_val) + "."`
   - Expected: src contains `for mw_path in loaded_module_paths`
   - Expected: src contains `mw_result.push(val_make_struct("File", mw_f_fields, mw_f_vals))`
   - Expected: src contains `return val_make_array(mw_result)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should return File arrays for module wildcard queries")
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("if tr_query == \"module_wildcard\"")).to_equal(true)
expect(src.contains("val mw_prefix = val_to_text(mw_prefix_val) + \".\"")).to_equal(true)
expect(src.contains("for mw_path in loaded_module_paths")).to_equal(true)
expect(src.contains("mw_result.push(val_make_struct(\"File\", mw_f_fields, mw_f_vals))")).to_equal(true)
expect(src.contains("return val_make_array(mw_result)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/file_class_introspection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering File Class Introspection.
- File Class Introspection

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

- Canonical SPipe generation for source `3d9dbcd095fe31e639c91285933cbae2984c5dd0c7cfa168ce521ece1d9c3f2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d9dbcd095fe31e639c91285933cbae2984c5dd0c7cfa168ce521ece1d9c3f2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d9dbcd095fe31e639c91285933cbae2984c5dd0c7cfa168ce521ece1d9c3f2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler_core/file_class_introspection_spec.spl
mirror: doc/06_spec/unit/compiler_core/file_class_introspection_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/file_class_introspection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/file_class_introspection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/file_class_introspection_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should desugar dotted FILE access into module_file traits' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler_core/file_class_introspection_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should desugar dotted FILE access into module_file traits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/file_class_introspection_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should desugar class and wildcard access into traits calls' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler_core/file_class_introspection_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should desugar class and wildcard access into traits calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/file_class_introspection_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return File structs for module_file queries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler_core/file_class_introspection_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return File structs for module_file queries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/file_class_introspection_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return Class structs with fields methods and counts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler_core/file_class_introspection_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return File arrays for module wildcard queries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
