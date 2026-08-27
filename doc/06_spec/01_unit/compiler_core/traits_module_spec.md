# Traits Module Specification

> Tests covering Traits Module.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Module Specification

## Scenarios

### Traits Module

#### should return the active module path for module_name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should return the active module path for module_name
   - Expected: src contains `if tr_query == "module_name"`
   - Expected: src contains `return val_make_text(module_get_path())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should return the active module path for module_name")
val src = traits_source()
expect(src.contains("if tr_query == \"module_name\"")).to_equal(true)
expect(src.contains("return val_make_text(module_get_path())")).to_equal(true)
```

</details>

#### should expose identifier query with no argument as empty text

- should expose identifier query with no argument as empty text
   - Expected: src contains `if tr_query == "identifier"`
   - Expected: src contains `if arg_eids.len() >= 2`
   - Expected: src contains `return val_make_text("")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose identifier query with no argument as empty text")
val src = traits_source()
expect(src.contains("if tr_query == \"identifier\"")).to_equal(true)
expect(src.contains("if arg_eids.len() >= 2")).to_equal(true)
expect(src.contains("return val_make_text(\"\")")).to_equal(true)
```

</details>

#### should return bare identifier names without evaluating them

- should return bare identifier names without evaluating them
   - Expected: src contains `if expr_get(id_eid).tag == 6`
   - Expected: src contains `return val_make_text(expr_get(id_eid).s_val)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should return bare identifier names without evaluating them")
val src = traits_source()
expect(src.contains("if expr_get(id_eid).tag == 6")).to_equal(true)
expect(src.contains("return val_make_text(expr_get(id_eid).s_val)")).to_equal(true)
```

</details>

#### should evaluate non identifier arguments before converting to text

- should evaluate non identifier arguments before converting to text
   - Expected: src contains `val id_val = eval_expr(id_eid)`
   - Expected: src contains `if eval_had_error: return -1`
   - Expected: src contains `return val_make_text(val_to_text(id_val))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should evaluate non identifier arguments before converting to text")
val src = traits_source()
expect(src.contains("val id_val = eval_expr(id_eid)")).to_equal(true)
expect(src.contains("if eval_had_error: return -1")).to_equal(true)
expect(src.contains("return val_make_text(val_to_text(id_val))")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/traits_module_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Traits Module.
- Traits Module

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

- Canonical SPipe generation for source `6a6a78a841401e2db9e4033ae1ef528d489b4c7e4738d048c6dd8a7bf4468bad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a6a78a841401e2db9e4033ae1ef528d489b4c7e4738d048c6dd8a7bf4468bad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a6a78a841401e2db9e4033ae1ef528d489b4c7e4738d048c6dd8a7bf4468bad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler_core/traits_module_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/traits_module_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/traits_module_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/traits_module_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/traits_module_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return the active module path for module_name' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_module_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return the active module path for module_name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_module_spec.spl:21:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose identifier query with no argument as empty text' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_module_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose identifier query with no argument as empty text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_module_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return bare identifier names without evaluating them' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_module_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return bare identifier names without evaluating them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_module_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should evaluate non identifier arguments before converting to text' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
