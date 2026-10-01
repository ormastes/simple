# Pass Descriptor Budget Specification

> Tests covering MIR built-in pass backend cost budget.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pass Descriptor Budget Specification

## Scenarios

### MIR built-in pass backend cost budget

#### classifies high-cost aggressive passes separately from cleanup passes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies high-cost aggressive passes separately from cleanup passes
   - Expected: mir_pass_cost_class("dead_code_elimination") equals `low`
   - Expected: mir_pass_cost_class("inline_aggressive") equals `high`
   - Expected: mir_pass_cost_class("auto_vectorize") equals `high`
   - Expected: mir_pass_cost_allowed("medium", "medium") is true
   - Expected: mir_pass_cost_allowed("high", "medium") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies high-cost aggressive passes separately from cleanup passes")
expect(mir_pass_cost_class("dead_code_elimination")).to_equal("low")
expect(mir_pass_cost_class("inline_aggressive")).to_equal("high")
expect(mir_pass_cost_class("auto_vectorize")).to_equal("high")
expect(mir_pass_cost_allowed("medium", "medium")).to_equal(true)
expect(mir_pass_cost_allowed("high", "medium")).to_equal(false)
```

</details>

#### filters Cranelift aggressive pipelines by compile-cost budget

- filters Cranelift aggressive pipelines by compile-cost budget
   - Expected: normal contains `inline_aggressive`
   - Expected: normal contains `auto_vectorize`
   - Expected: medium does not contain `inline_aggressive`
   - Expected: medium does not contain `auto_vectorize`
   - Expected: medium contains `dead_code_elimination`
   - Expected: medium contains `loop_unroll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters Cranelift aggressive pipelines by compile-cost budget")
val normal = optimizationpipeline_passes_for_backend(OptLevel.Aggressive, "cranlift")
val medium = optimizationpipeline_passes_for_backend_budget(OptLevel.Aggressive, "cranlift", "medium")

expect(normal.contains("inline_aggressive")).to_equal(true)
expect(normal.contains("auto_vectorize")).to_equal(true)
expect(medium.contains("inline_aggressive")).to_equal(false)
expect(medium.contains("auto_vectorize")).to_equal(false)
expect(medium.contains("dead_code_elimination")).to_equal(true)
expect(medium.contains("loop_unroll")).to_equal(true)
```

</details>

#### combines LLVM backend skips with compile-cost budget skips

- combines LLVM backend skips with compile-cost budget skips
   - Expected: medium contains `dead_code_elimination`
   - Expected: medium contains `bounds_check_elimination`
   - Expected: medium does not contain `strength_reduction`
   - Expected: medium does not contain `loop_unroll`
   - Expected: medium does not contain `inline_aggressive`
   - Expected: mir_pass_applies_to_backend_budget("strength_reduction", "llvm", "high") is false
   - Expected: mir_pass_applies_to_backend_budget("inline_aggressive", "cranelift", "medium") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines LLVM backend skips with compile-cost budget skips")
val medium = optimizationpipeline_passes_for_backend_budget(OptLevel.Aggressive, "llvm-lib", "medium")

expect(medium.contains("dead_code_elimination")).to_equal(true)
expect(medium.contains("bounds_check_elimination")).to_equal(true)
expect(medium.contains("strength_reduction")).to_equal(false)
expect(medium.contains("loop_unroll")).to_equal(false)
expect(medium.contains("inline_aggressive")).to_equal(false)
expect(mir_pass_applies_to_backend_budget("strength_reduction", "llvm", "high")).to_equal(false)
expect(mir_pass_applies_to_backend_budget("inline_aggressive", "cranelift", "medium")).to_equal(false)
```

</details>

#### uses shared backend aliases without treating future backends as LLVM

- uses shared backend aliases without treating future backends as LLVM
   - Expected: mir_pass_applies_to_backend_budget("strength_reduction", "llvmlib", "high") is false
   - Expected: mir_pass_applies_to_backend_budget("strength_reduction", "wasm", "high") is true
   - Expected: wasm contains `strength_reduction`
   - Expected: wasm contains `global_value_numbering`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses shared backend aliases without treating future backends as LLVM")
expect(mir_pass_applies_to_backend_budget("strength_reduction", "llvmlib", "high")).to_equal(false)
expect(mir_pass_applies_to_backend_budget("strength_reduction", "wasm", "high")).to_equal(true)
val wasm = optimizationpipeline_passes_for_backend_budget(OptLevel.Aggressive, "wasm", "high")
expect(wasm.contains("strength_reduction")).to_equal(true)
expect(wasm.contains("global_value_numbering")).to_equal(true)
```

</details>

#### explains backend and cost decisions for individual passes

- explains backend and cost decisions for individual passes
   - Expected: llvm_skip.applies is false
   - Expected: llvm_skip.reason equals `llvm_runs_vectorizer_pipeline`
   - Expected: llvm_skip.cost_class equals `high`
   - Expected: cost_skip.applies is false
   - Expected: cost_skip.reason equals `cost budget exceeded`
   - Expected: ready.applies is true
   - Expected: ready.reason equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explains backend and cost decisions for individual passes")
val llvm_skip = mir_pass_backend_decision("auto_vectorize", "llvm", "high")
expect(llvm_skip.applies).to_equal(false)
expect(llvm_skip.reason).to_equal("llvm_runs_vectorizer_pipeline")
expect(llvm_skip.cost_class).to_equal("high")

val cost_skip = mir_pass_backend_decision("inline_aggressive", "cranelift", "medium")
expect(cost_skip.applies).to_equal(false)
expect(cost_skip.reason).to_equal("cost budget exceeded")

val ready = mir_pass_backend_decision("dead_code_elimination", "cranelift", "medium")
expect(ready.applies).to_equal(true)
expect(ready.reason).to_equal("ready")
```

</details>

#### reports skipped pipeline decisions with stable reasons

- reports skipped pipeline decisions with stable reasons
   - Expected: found_cost_skip is true
   - Expected: found_llvm_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports skipped pipeline decisions with stable reasons")
val cranelift_skips = optimizationpipeline_skipped_decisions_for_backend_budget(OptLevel.Aggressive, "cranelift", "medium")
var found_cost_skip = false
for decision in cranelift_skips:
    if decision.pass_name == "inline_aggressive" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)

val llvm_skips = optimizationpipeline_skipped_decisions_for_backend_budget(OptLevel.Aggressive, "llvm-lib", "high")
var found_llvm_skip = false
for decision in llvm_skips:
    if decision.pass_name == "auto_vectorize" and decision.reason == "llvm_runs_vectorizer_pipeline":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>

#### builds applied and skipped backend pass plans in one decision pass

- builds applied and skipped backend pass plans in one decision pass
   - Expected: plan.passes contains `dead_code_elimination`
   - Expected: plan.passes contains `bounds_check_elimination`
   - Expected: plan.passes does not contain `auto_vectorize`
   - Expected: found_backend_skip is true
   - Expected: found_cost_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds applied and skipped backend pass plans in one decision pass")
val plan = optimizationpipeline_backend_plan_for_budget(OptLevel.Aggressive, "llvm", "medium")
expect(plan.passes.contains("dead_code_elimination")).to_equal(true)
expect(plan.passes.contains("bounds_check_elimination")).to_equal(true)
expect(plan.passes.contains("auto_vectorize")).to_equal(false)

var found_backend_skip = false
var found_cost_skip = false
for decision in plan.skipped_passes:
    if decision.pass_name == "auto_vectorize" and decision.reason == "llvm_runs_vectorizer_pipeline":
        found_backend_skip = true
    if decision.pass_name == "inline_aggressive" and decision.reason == "llvm_runs_inliner_pipeline":
        found_cost_skip = true
expect(found_backend_skip).to_equal(true)
expect(found_cost_skip).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/60.mir_opt/pass_descriptor_budget_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR built-in pass backend cost budget.
- MIR built-in pass backend cost budget

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `bcc8c067327dc135be56e6f8b3f85148fda44e9cdcc41a3de401c9d421634386`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bcc8c067327dc135be56e6f8b3f85148fda44e9cdcc41a3de401c9d421634386`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bcc8c067327dc135be56e6f8b3f85148fda44e9cdcc41a3de401c9d421634386`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/60.mir_opt/pass_descriptor_budget_spec.spl
mirror: doc/06_spec/01_unit/compiler/60.mir_opt/pass_descriptor_budget_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/60.mir_opt/pass_descriptor_budget_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/60.mir_opt/pass_descriptor_budget_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/60.mir_opt/pass_descriptor_budget_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies high-cost aggressive passes separately from cleanup passes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/60.mir_opt/pass_descriptor_budget_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters Cranelift aggressive pipelines by compile-cost budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/60.mir_opt/pass_descriptor_budget_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'combines LLVM backend skips with compile-cost budget skips' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
