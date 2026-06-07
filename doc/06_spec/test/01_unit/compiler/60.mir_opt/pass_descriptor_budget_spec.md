# Pass Descriptor Budget Specification

> <details>

<!-- sdn-diagram:id=pass_descriptor_budget_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pass_descriptor_budget_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pass_descriptor_budget_spec -> std
pass_descriptor_budget_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pass_descriptor_budget_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pass Descriptor Budget Specification

## Scenarios

### MIR built-in pass backend cost budget

#### classifies high-cost aggressive passes separately from cleanup passes

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mir_pass_cost_class("dead_code_elimination")).to_equal("low")
expect(mir_pass_cost_class("inline_aggressive")).to_equal("high")
expect(mir_pass_cost_class("auto_vectorize")).to_equal("high")
expect(mir_pass_cost_allowed("medium", "medium")).to_equal(true)
expect(mir_pass_cost_allowed("high", "medium")).to_equal(false)
```

</details>

#### filters Cranelift aggressive pipelines by compile-cost budget

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mir_pass_applies_to_backend_budget("strength_reduction", "llvmlib", "high")).to_equal(false)
expect(mir_pass_applies_to_backend_budget("strength_reduction", "wasm", "high")).to_equal(true)
val wasm = optimizationpipeline_passes_for_backend_budget(OptLevel.Aggressive, "wasm", "high")
expect(wasm.contains("strength_reduction")).to_equal(true)
expect(wasm.contains("global_value_numbering")).to_equal(true)
```

</details>

#### explains backend and cost decisions for individual passes

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
