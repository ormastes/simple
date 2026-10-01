# Mir Specification

> Tests covering Mir.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Specification

## Scenarios

### Mir

#### should define MIR instruction constructors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should define MIR instruction constructors
   - Expected: src contains `val MIR_CONST_INT = 1`
   - Expected: src contains `fn mir_const_int(dest: i64, value: i64) -> i64`
   - Expected: src contains `fn mir_const_float(dest: i64, value: text) -> i64`
   - Expected: src contains `fn mir_binop(kind: i64, dest: i64, left: i64, right: i64) -> i64`
   - Expected: src contains `inst_dest[idx] = dest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should define MIR instruction constructors")
val src = mir_source()
expect(src.contains("val MIR_CONST_INT = 1")).to_equal(true)
expect(src.contains("fn mir_const_int(dest: i64, value: i64) -> i64")).to_equal(true)
expect(src.contains("fn mir_const_float(dest: i64, value: text) -> i64")).to_equal(true)
expect(src.contains("fn mir_binop(kind: i64, dest: i64, left: i64, right: i64) -> i64")).to_equal(true)
expect(src.contains("inst_dest[idx] = dest")).to_equal(true)
```

</details>

#### should define MIR terminators

- should define MIR terminators
   - Expected: src contains `fn term_goto(target_bb: i64) -> i64`
   - Expected: src contains `fn term_return(value_var: i64) -> i64`
   - Expected: src contains `fn term_return_void() -> i64`
   - Expected: src contains `fn term_if_branch(cond_var: i64, then_bb: i64, else_bb: i64) -> i64`
   - Expected: src contains `fn term_switch(scrutinee: i64, case_values: [i64], case_targets: [i64], defau... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should define MIR terminators")
val src = mir_source()
expect(src.contains("fn term_goto(target_bb: i64) -> i64")).to_equal(true)
expect(src.contains("fn term_return(value_var: i64) -> i64")).to_equal(true)
expect(src.contains("fn term_return_void() -> i64")).to_equal(true)
expect(src.contains("fn term_if_branch(cond_var: i64, then_bb: i64, else_bb: i64) -> i64")).to_equal(true)
expect(src.contains("fn term_switch(scrutinee: i64, case_values: [i64], case_targets: [i64], default_bb: i64) -> i64")).to_equal(true)
```

</details>

#### should define basic block and function builders

- should define basic block and function builders
   - Expected: src contains `fn bb_new(label: text) -> i64`
   - Expected: src contains `fn bb_add_inst`
   - Expected: src contains `fn bb_set_terminator`
   - Expected: src contains `fn mir_fn_new(name: text, param_names: [text], param_types: [i64], ret_type: ... (full value in folded executable source)`
   - Expected: src contains `fn mir_fn_add_bb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should define basic block and function builders")
val src = mir_source()
expect(src.contains("fn bb_new(label: text) -> i64")).to_equal(true)
expect(src.contains("fn bb_add_inst")).to_equal(true)
expect(src.contains("fn bb_set_terminator")).to_equal(true)
expect(src.contains("fn mir_fn_new(name: text, param_names: [text], param_types: [i64], ret_type: i64, is_ext: i64) -> i64")).to_equal(true)
expect(src.contains("fn mir_fn_add_bb")).to_equal(true)
```

</details>

#### should define module storage and debug names

- should define module storage and debug names
   - Expected: src contains `fn mir_module_add_fn(fn_id: i64)`
   - Expected: src contains `fn mir_module_get_fns`
   - Expected: src contains `fn mir_inst_kind_name(kind: i64) -> text`
   - Expected: src contains `if kind == MIR_CONST_INT: return "ConstInt"`
   - Expected: src contains `if kind == MIR_ADD: return "Add"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should define module storage and debug names")
val src = mir_source()
expect(src.contains("fn mir_module_add_fn(fn_id: i64)")).to_equal(true)
expect(src.contains("fn mir_module_get_fns")).to_equal(true)
expect(src.contains("fn mir_inst_kind_name(kind: i64) -> text")).to_equal(true)
expect(src.contains("if kind == MIR_CONST_INT: return \"ConstInt\"")).to_equal(true)
expect(src.contains("if kind == MIR_ADD: return \"Add\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/mir_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mir.
- Mir

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

- Canonical SPipe generation for source `72d4e17ad5401eb3c18d5ff19eb2d5fe4aa1cc47f23874a490b631744051acbd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `72d4e17ad5401eb3c18d5ff19eb2d5fe4aa1cc47f23874a490b631744051acbd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `72d4e17ad5401eb3c18d5ff19eb2d5fe4aa1cc47f23874a490b631744051acbd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler_core/mir_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/mir_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/mir_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/mir_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/mir_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define MIR instruction constructors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/mir_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define MIR instruction constructors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/mir_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define MIR terminators' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/mir_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define MIR terminators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/mir_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define basic block and function builders' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/mir_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define basic block and function builders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/mir_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define module storage and debug names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
