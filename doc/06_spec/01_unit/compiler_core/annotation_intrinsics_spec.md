# Annotation Intrinsics Specification

> Tests covering Annotation Intrinsics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Annotation Intrinsics Specification

## Scenarios

### Annotation Intrinsics

#### should parse source location annotation identifiers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should parse source location annotation identifiers
   - Expected: parser_src contains `val at_builtin_name = "__builtin_" + ann_name`
   - Expected: parser_src contains `return expr_ident(at_builtin_name, 0)`
   - Expected: parser_src contains `val at_callee = expr_ident("__traits", 0)`
   - Expected: parser_src contains `return expr_call(at_callee, at_args, 0)`
   - Expected: parser_eval_src contains `if name == "__builtin_file":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should parse source location annotation identifiers")
val parser_src = read_source("src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl")
# Anchored to real desugar code, not to the "# @file, @line, @function"
# comment: bare @ident becomes expr_ident("__builtin_" + ann_name).
expect(parser_src.contains("val at_builtin_name = \"__builtin_\" + ann_name")).to_equal(true)
expect(parser_src.contains("return expr_ident(at_builtin_name, 0)")).to_equal(true)
# @ann(...) with parens desugars to a __traits call instead.
expect(parser_src.contains("val at_callee = expr_ident(\"__traits\", 0)")).to_equal(true)
expect(parser_src.contains("return expr_call(at_callee, at_args, 0)")).to_equal(true)
# The evaluator side must accept the desugared builtin identifier.
val parser_eval_src = read_source("src/compiler/10.frontend/core/interpreter/eval.spl")
expect(parser_eval_src.contains("if name == \"__builtin_file\":")).to_equal(true)
```

</details>

#### should evaluate source location annotation identifiers

- should evaluate source location annotation identifiers
   - Expected: eval_src contains `if name == "@file"`
   - Expected: eval_src contains `if name == "@line"`
   - Expected: eval_src contains `if name == "@function"`
   - Expected: eval_src contains `module_get_path()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should evaluate source location annotation identifiers")
val eval_src = read_source("src/compiler/10.frontend/core/interpreter/eval.spl")
expect(eval_src.contains("if name == \"@file\"")).to_equal(true)
expect(eval_src.contains("if name == \"@line\"")).to_equal(true)
expect(eval_src.contains("if name == \"@function\"")).to_equal(true)
expect(eval_src.contains("module_get_path()")).to_equal(true)
```

</details>

#### should reject failing static assertions with a diagnostic

- should reject failing static assertions with a diagnostic
   - Expected: builtins_src contains `if name == "@static_assert"`
   - Expected: builtins_src contains `static_assert failed`
   - Expected: builtins_src contains `tr_query == "static_assert"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should reject failing static assertions with a diagnostic")
val builtins_src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(builtins_src.contains("if name == \"@static_assert\"")).to_equal(true)
expect(builtins_src.contains("static_assert failed")).to_equal(true)
expect(builtins_src.contains("tr_query == \"static_assert\"")).to_equal(true)
```

</details>

#### should keep must_use scanning available through interpreter exports

- should keep must_use scanning available through interpreter exports
   - Expected: tables_src contains `fn must_use_scan_source(source: text)`
   - Expected: tables_src contains `@must_use`
   - Expected: init_src contains `export must_use_scan_source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should keep must_use scanning available through interpreter exports")
val tables_src = read_source("src/compiler/10.frontend/core/interpreter/eval_tables.spl")
val init_src = read_source("src/compiler/10.frontend/core/interpreter/__init__.spl")
expect(tables_src.contains("fn must_use_scan_source(source: text)")).to_equal(true)
expect(tables_src.contains("@must_use")).to_equal(true)
expect(init_src.contains("export must_use_scan_source")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/annotation_intrinsics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Annotation Intrinsics.
- Annotation Intrinsics

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

- Canonical SPipe generation for source `95148ddea6176f6b84bfd878d19f93d7eed3c1fed29c12f4c47d1f2e410d024c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95148ddea6176f6b84bfd878d19f93d7eed3c1fed29c12f4c47d1f2e410d024c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95148ddea6176f6b84bfd878d19f93d7eed3c1fed29c12f4c47d1f2e410d024c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler_core/annotation_intrinsics_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/annotation_intrinsics_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/annotation_intrinsics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/annotation_intrinsics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/annotation_intrinsics_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse source location annotation identifiers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/annotation_intrinsics_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse source location annotation identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/annotation_intrinsics_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should evaluate source location annotation identifiers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/annotation_intrinsics_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should evaluate source location annotation identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/annotation_intrinsics_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject failing static assertions with a diagnostic' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/annotation_intrinsics_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject failing static assertions with a diagnostic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/annotation_intrinsics_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep must_use scanning available through interpreter exports' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
