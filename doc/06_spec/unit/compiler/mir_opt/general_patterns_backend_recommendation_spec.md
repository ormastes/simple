# General Patterns Backend Recommendation Specification

> Tests covering general optimization backend recommendations for REQ-OPJH-022 REQ-OPJH-025 REQ-OPJH-026.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# General Patterns Backend Recommendation Specification

## Scenarios

### general optimization backend recommendations for REQ-OPJH-022 REQ-OPJH-025 REQ-OPJH-026

#### keeps SSA var canonicalization for Cranelift hotspot planning

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-OPJH-022
# @req REQ-OPJH-025
# @req REQ-OPJH-026
```

</details>

#### skips Simple-side SSA var canonicalization for LLVM

- skips Simple-side SSA var canonicalization for LLVM
   - Expected: backend_optimization_has_recommendation("llvm", "ssa-var-canon") is false
   - Expected: backend_optimization_has_recommendation("llvm", "llvm-entry-alloca-shaping") is true
   - Expected: backend_optimization_has_recommendation("llvm", "llvm-default-pipeline") is true
   - Expected: reason != nil is true
   - Expected: reason.unwrap() equals `llvm_backend_runs_mem2reg_sroa_pipeline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips Simple-side SSA var canonicalization for LLVM")
expect(backend_optimization_has_recommendation("llvm", "ssa-var-canon")).to_equal(false)
expect(backend_optimization_has_recommendation("llvm", "llvm-entry-alloca-shaping")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "llvm-default-pipeline")).to_equal(true)

val all = backend_optimization_recommendations_for("cranelift")
val skipped = all[0].provider
val reason = optimization_rule_provider_skip_reason(skipped, OptimizerBackendKind.Llvm)
expect(reason != nil).to_equal(true)
expect(reason.unwrap()).to_equal("llvm_backend_runs_mem2reg_sroa_pipeline")
```

</details>

#### keeps high-level MIR optimizations for both Cranelift and LLVM

- keeps high-level MIR optimizations for both Cranelift and LLVM
   - Expected: backend_optimization_has_recommendation("cranelift", "bounds-check-elim") is true
   - Expected: backend_optimization_has_recommendation("llvm", "bounds-check-elim") is true
   - Expected: backend_optimization_has_recommendation("cranelift", "byte-scan-to-delimiter") is true
   - Expected: backend_optimization_has_recommendation("llvm", "byte-scan-to-delimiter") is true
   - Expected: backend_optimization_has_recommendation("cranelift", "checksum-reducer") is true
   - Expected: backend_optimization_has_recommendation("llvm", "checksum-reducer") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps high-level MIR optimizations for both Cranelift and LLVM")
expect(backend_optimization_has_recommendation("cranelift", "bounds-check-elim")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "bounds-check-elim")).to_equal(true)
expect(backend_optimization_has_recommendation("cranelift", "byte-scan-to-delimiter")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "byte-scan-to-delimiter")).to_equal(true)
expect(backend_optimization_has_recommendation("cranelift", "checksum-reducer")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "checksum-reducer")).to_equal(true)
```

</details>

#### keeps Simple-owned LICM away from LLVM default pipeline

- keeps Simple-owned LICM away from LLVM default pipeline
   - Expected: backend_optimization_has_recommendation("cranelift", "cranelift-local-licm") is true
   - Expected: backend_optimization_has_recommendation("interpreter", "cranelift-local-licm") is true
   - Expected: backend_optimization_has_recommendation("llvm", "cranelift-local-licm") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Simple-owned LICM away from LLVM default pipeline")
expect(backend_optimization_has_recommendation("cranelift", "cranelift-local-licm")).to_equal(true)
expect(backend_optimization_has_recommendation("interpreter", "cranelift-local-licm")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "cranelift-local-licm")).to_equal(false)
```

</details>

<details>
<summary>Advanced: keeps Simple loop unroll away from LLVM loop pipeline</summary>

#### keeps Simple loop unroll away from LLVM loop pipeline

- keeps Simple loop unroll away from LLVM loop pipeline
   - Expected: backend_optimization_has_recommendation("cranelift", "simple-loop-unroll") is true
   - Expected: backend_optimization_has_recommendation("interpreter", "simple-loop-unroll") is true
   - Expected: backend_optimization_has_recommendation("llvm", "simple-loop-unroll") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Simple loop unroll away from LLVM loop pipeline")
expect(backend_optimization_has_recommendation("cranelift", "simple-loop-unroll")).to_equal(true)
expect(backend_optimization_has_recommendation("interpreter", "simple-loop-unroll")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "simple-loop-unroll")).to_equal(false)
```

</details>


</details>

#### keeps Simple predicate promotion away from LLVM if-conversion pipeline

- keeps Simple predicate promotion away from LLVM if-conversion pipeline
   - Expected: backend_optimization_has_recommendation("cranelift", "simple-predicate-promote") is true
   - Expected: backend_optimization_has_recommendation("interpreter", "simple-predicate-promote") is true
   - Expected: backend_optimization_has_recommendation("llvm", "simple-predicate-promote") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Simple predicate promotion away from LLVM if-conversion pipeline")
expect(backend_optimization_has_recommendation("cranelift", "simple-predicate-promote")).to_equal(true)
expect(backend_optimization_has_recommendation("interpreter", "simple-predicate-promote")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "simple-predicate-promote")).to_equal(false)
```

</details>

#### keeps Simple strength reduction away from LLVM scalar pipeline

- keeps Simple strength reduction away from LLVM scalar pipeline
   - Expected: backend_optimization_has_recommendation("cranelift", "simple-strength-reduce") is true
   - Expected: backend_optimization_has_recommendation("interpreter", "simple-strength-reduce") is true
   - Expected: backend_optimization_has_recommendation("llvm", "simple-strength-reduce") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Simple strength reduction away from LLVM scalar pipeline")
expect(backend_optimization_has_recommendation("cranelift", "simple-strength-reduce")).to_equal(true)
expect(backend_optimization_has_recommendation("interpreter", "simple-strength-reduce")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "simple-strength-reduce")).to_equal(false)
```

</details>

#### keeps Simple scalar cleanup away from LLVM scalar pipeline

- keeps Simple scalar cleanup away from LLVM scalar pipeline
   - Expected: backend_optimization_has_recommendation("cranelift", "simple-scalar-cleanup") is true
   - Expected: backend_optimization_has_recommendation("interpreter", "simple-scalar-cleanup") is true
   - Expected: backend_optimization_has_recommendation("llvm", "simple-scalar-cleanup") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Simple scalar cleanup away from LLVM scalar pipeline")
expect(backend_optimization_has_recommendation("cranelift", "simple-scalar-cleanup")).to_equal(true)
expect(backend_optimization_has_recommendation("interpreter", "simple-scalar-cleanup")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "simple-scalar-cleanup")).to_equal(false)
```

</details>

#### keeps Simple auto-vectorization away from LLVM vectorizer pipeline

- keeps Simple auto-vectorization away from LLVM vectorizer pipeline
   - Expected: backend_optimization_has_recommendation("cranelift", "simple-auto-vectorize") is true
   - Expected: backend_optimization_has_recommendation("interpreter", "simple-auto-vectorize") is true
   - Expected: backend_optimization_has_recommendation("llvm", "simple-auto-vectorize") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Simple auto-vectorization away from LLVM vectorizer pipeline")
expect(backend_optimization_has_recommendation("cranelift", "simple-auto-vectorize")).to_equal(true)
expect(backend_optimization_has_recommendation("interpreter", "simple-auto-vectorize")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "simple-auto-vectorize")).to_equal(false)
```

</details>

#### keeps Simple hot-call inlining away from LLVM inliner pipeline

- keeps Simple hot-call inlining away from LLVM inliner pipeline
   - Expected: backend_optimization_has_recommendation("cranelift", "simple-hot-call-inline") is true
   - Expected: backend_optimization_has_recommendation("interpreter", "simple-hot-call-inline") is true
   - Expected: backend_optimization_has_recommendation("llvm", "simple-hot-call-inline") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps Simple hot-call inlining away from LLVM inliner pipeline")
expect(backend_optimization_has_recommendation("cranelift", "simple-hot-call-inline")).to_equal(true)
expect(backend_optimization_has_recommendation("interpreter", "simple-hot-call-inline")).to_equal(true)
expect(backend_optimization_has_recommendation("llvm", "simple-hot-call-inline")).to_equal(false)
```

</details>

#### does not apply Cranelift-local LICM to unrelated future backends

- does not apply Cranelift-local LICM to unrelated future backends
   - Expected: wasm.recommendation_names does not contain `cranelift-local-licm`
   - Expected: found_wasm_skip is true
   - Expected: c_plan.recommendation_names does not contain `cranelift-local-licm`
   - Expected: c_plan.recommendation_names does not contain `simple-loop-unroll`
   - Expected: c_plan.recommendation_names does not contain `simple-predicate-promote`
   - Expected: c_plan.recommendation_names does not contain `simple-strength-reduce`
   - Expected: c_plan.recommendation_names does not contain `simple-scalar-cleanup`
   - Expected: wasm_high.recommendation_names does not contain `simple-strength-reduce`
   - Expected: found_strength_skip is true
   - Expected: wasm_high.recommendation_names does not contain `simple-predicate-promote`
   - Expected: found_predicate_skip is true
   - Expected: wasm_high.recommendation_names does not contain `simple-loop-unroll`
   - Expected: found_unroll_skip is true
   - Expected: wasm_high.recommendation_names does not contain `simple-scalar-cleanup`
   - Expected: found_scalar_skip is true
   - Expected: wasm_high.recommendation_names does not contain `simple-auto-vectorize`
   - Expected: found_vectorize_skip is true
   - Expected: wasm_high.recommendation_names does not contain `simple-hot-call-inline`
   - Expected: found_inline_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not apply Cranelift-local LICM to unrelated future backends")
val wasm = backend_optimization_plan_for_budget("wasm", "medium")
expect(wasm.recommendation_names.contains("cranelift-local-licm")).to_equal(false)
var found_wasm_skip = false
for decision in wasm.skipped_decisions:
    if decision.stable_name == "cranelift-local-licm" and decision.reason == "backend_not_simple_low_tier_jit":
        found_wasm_skip = true
expect(found_wasm_skip).to_equal(true)

val c_plan = backend_optimization_plan_for_budget("c", "medium")
expect(c_plan.recommendation_names.contains("cranelift-local-licm")).to_equal(false)
expect(c_plan.recommendation_names.contains("simple-loop-unroll")).to_equal(false)
expect(c_plan.recommendation_names.contains("simple-predicate-promote")).to_equal(false)
expect(c_plan.recommendation_names.contains("simple-strength-reduce")).to_equal(false)
expect(c_plan.recommendation_names.contains("simple-scalar-cleanup")).to_equal(false)

val wasm_high = backend_optimization_plan_for_budget("wasm", "high")
expect(wasm_high.recommendation_names.contains("simple-strength-reduce")).to_equal(false)
var found_strength_skip = false
for decision in wasm_high.skipped_decisions:
    if decision.stable_name == "simple-strength-reduce" and decision.reason == "backend_not_simple_low_tier_jit":
        found_strength_skip = true
expect(found_strength_skip).to_equal(true)

expect(wasm_high.recommendation_names.contains("simple-predicate-promote")).to_equal(false)
var found_predicate_skip = false
for decision in wasm_high.skipped_decisions:
    if decision.stable_name == "simple-predicate-promote" and decision.reason == "backend_not_simple_low_tier_jit":
        found_predicate_skip = true
expect(found_predicate_skip).to_equal(true)

expect(wasm_high.recommendation_names.contains("simple-loop-unroll")).to_equal(false)
var found_unroll_skip = false
for decision in wasm_high.skipped_decisions:
    if decision.stable_name == "simple-loop-unroll" and decision.reason == "backend_not_simple_low_tier_jit":
        found_unroll_skip = true
expect(found_unroll_skip).to_equal(true)

expect(wasm_high.recommendation_names.contains("simple-scalar-cleanup")).to_equal(false)
var found_scalar_skip = false
for decision in wasm_high.skipped_decisions:
    if decision.stable_name == "simple-scalar-cleanup" and decision.reason == "backend_not_simple_low_tier_jit":
        found_scalar_skip = true
expect(found_scalar_skip).to_equal(true)

expect(wasm_high.recommendation_names.contains("simple-auto-vectorize")).to_equal(false)
var found_vectorize_skip = false
for decision in wasm_high.skipped_decisions:
    if decision.stable_name == "simple-auto-vectorize" and decision.reason == "backend_not_simple_low_tier_jit":
        found_vectorize_skip = true
expect(found_vectorize_skip).to_equal(true)

expect(wasm_high.recommendation_names.contains("simple-hot-call-inline")).to_equal(false)
var found_inline_skip = false
for decision in wasm_high.skipped_decisions:
    if decision.stable_name == "simple-hot-call-inline" and decision.reason == "backend_not_simple_low_tier_jit":
        found_inline_skip = true
expect(found_inline_skip).to_equal(true)
```

</details>

#### filters backend recommendations by compile cost budget

- filters backend recommendations by compile cost budget
   - Expected: backend_optimization_cost_allowed("medium", "medium") is true
   - Expected: backend_optimization_cost_allowed("high", "medium") is false
   - Expected: llvm_medium contains `llvm-entry-alloca-shaping`
   - Expected: llvm_medium does not contain `llvm-default-pipeline`
   - Expected: llvm_high contains `llvm-default-pipeline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters backend recommendations by compile cost budget")
expect(backend_optimization_cost_allowed("medium", "medium")).to_equal(true)
expect(backend_optimization_cost_allowed("high", "medium")).to_equal(false)

val llvm_medium = backend_optimization_recommendation_names_for_budget("llvm", "medium")
expect(llvm_medium.contains("llvm-entry-alloca-shaping")).to_equal(true)
expect(llvm_medium.contains("llvm-default-pipeline")).to_equal(false)

val llvm_high = backend_optimization_recommendation_names_for_budget("llvm", "high")
expect(llvm_high.contains("llvm-default-pipeline")).to_equal(true)
```

</details>

#### explains skipped backend recommendations by backend and compile budget

- explains skipped backend recommendations by backend and compile budget
   - Expected: found_llvm_owned_ssa is true
   - Expected: found_budget_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explains skipped backend recommendations by backend and compile budget")
var found_llvm_owned_ssa = false
for decision in backend_optimization_skipped_decisions_for_budget("llvm", "high"):
    if decision.stable_name == "ssa-var-canon" and decision.reason == "llvm_backend_runs_mem2reg_sroa_pipeline":
        found_llvm_owned_ssa = true
expect(found_llvm_owned_ssa).to_equal(true)

var found_budget_skip = false
for decision in backend_optimization_decisions_for_budget("llvm", "medium"):
    if decision.stable_name == "llvm-default-pipeline" and decision.reason == "cost budget exceeded":
        found_budget_skip = true
expect(found_budget_skip).to_equal(true)
```

</details>

#### builds applied and skipped recommendation plans in one decision pass

- builds applied and skipped recommendation plans in one decision pass
   - Expected: plan.recommendation_names contains `llvm-entry-alloca-shaping`
   - Expected: plan.recommendation_names does not contain `llvm-default-pipeline`
   - Expected: plan.recommendation_names does not contain `ssa-var-canon`
   - Expected: found_backend_skip is true
   - Expected: found_cost_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds applied and skipped recommendation plans in one decision pass")
val plan = backend_optimization_plan_for_budget("llvm", "medium")
expect(plan.recommendation_names.contains("llvm-entry-alloca-shaping")).to_equal(true)
expect(plan.recommendation_names.contains("llvm-default-pipeline")).to_equal(false)
expect(plan.recommendation_names.contains("ssa-var-canon")).to_equal(false)

var found_backend_skip = false
var found_cost_skip = false
for decision in plan.skipped_decisions:
    if decision.stable_name == "ssa-var-canon" and decision.reason == "llvm_backend_runs_mem2reg_sroa_pipeline":
        found_backend_skip = true
    if decision.stable_name == "llvm-default-pipeline" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_backend_skip).to_equal(true)
expect(found_cost_skip).to_equal(true)
```

</details>

#### gates backend recommendation plans on required optimizer facts

- gates backend recommendation plans on required optimizer facts
   - Expected: missing.recommendation_names does not contain `ssa-var-canon`
   - Expected: found_missing_ssa is true
   - Expected: missing_var.recommendation_names does not contain `ssa-var-canon`
   - Expected: found_missing_var is true
   - Expected: missing_escape_analysis.recommendation_names does not contain `ssa-var-canon`
   - Expected: found_missing_escape_analysis is true
   - Expected: ready.recommendation_names contains `ssa-var-canon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates backend recommendation plans on required optimizer facts")
val missing = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir"])
expect(missing.recommendation_names.contains("ssa-var-canon")).to_equal(false)
var found_missing_ssa = false
for decision in missing.skipped_decisions:
    if decision.stable_name == "ssa-var-canon" and decision.reason == "missing ssa.var_transform":
        found_missing_ssa = true
expect(found_missing_ssa).to_equal(true)

val missing_var = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "ssa.var_transform", "escape.analyzed", "escape.no_escape", "borrow.reassign_safe"])
expect(missing_var.recommendation_names.contains("ssa-var-canon")).to_equal(false)
var found_missing_var = false
for decision in missing_var.skipped_decisions:
    if decision.stable_name == "ssa-var-canon" and decision.reason == "missing var.reassignment":
        found_missing_var = true
expect(found_missing_var).to_equal(true)

val missing_escape_analysis = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "ssa.var_transform", "var.reassignment", "escape.no_escape", "borrow.reassign_safe"])
expect(missing_escape_analysis.recommendation_names.contains("ssa-var-canon")).to_equal(false)
var found_missing_escape_analysis = false
for decision in missing_escape_analysis.skipped_decisions:
    if decision.stable_name == "ssa-var-canon" and decision.reason == "missing escape.analyzed":
        found_missing_escape_analysis = true
expect(found_missing_escape_analysis).to_equal(true)

val ready = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "ssa.var_transform", "var.reassignment", "escape.analyzed", "escape.no_escape", "borrow.reassign_safe"])
expect(ready.recommendation_names.contains("ssa-var-canon")).to_equal(true)
```

</details>

<details>
<summary>Advanced: gates Simple loop unroll on canonical trip-count and budget facts</summary>

#### gates Simple loop unroll on canonical trip-count and budget facts

- gates Simple loop unroll on canonical trip-count and budget facts
   - Expected: missing.recommendation_names does not contain `simple-loop-unroll`
   - Expected: found_missing_budget is true
   - Expected: low.recommendation_names does not contain `simple-loop-unroll`
   - Expected: found_cost_skip is true
   - Expected: ready.recommendation_names contains `simple-loop-unroll`
   - Expected: llvm.recommendation_names does not contain `simple-loop-unroll`
   - Expected: found_llvm_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates Simple loop unroll on canonical trip-count and budget facts")
val missing = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "loop_canonical", "loop_trip_count"])
expect(missing.recommendation_names.contains("simple-loop-unroll")).to_equal(false)
var found_missing_budget = false
for decision in missing.skipped_decisions:
    if decision.stable_name == "simple-loop-unroll" and decision.reason == "missing unroll_budget":
        found_missing_budget = true
expect(found_missing_budget).to_equal(true)

val low = backend_optimization_plan_for_budget_with_facts("cranelift", "low", ["typed_mir", "loop_canonical", "loop_trip_count", "unroll_budget"])
expect(low.recommendation_names.contains("simple-loop-unroll")).to_equal(false)
var found_cost_skip = false
for decision in low.skipped_decisions:
    if decision.stable_name == "simple-loop-unroll" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)

val ready = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "loop_canonical", "loop_trip_count", "unroll_budget"])
expect(ready.recommendation_names.contains("simple-loop-unroll")).to_equal(true)

val llvm = backend_optimization_plan_for_budget_with_facts("llvm", "medium", ["typed_mir", "loop_canonical", "loop_trip_count", "unroll_budget", "llvm_backend_available"])
expect(llvm.recommendation_names.contains("simple-loop-unroll")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_decisions:
    if decision.stable_name == "simple-loop-unroll" and decision.reason == "llvm_runs_loop_unroll_pipeline":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>


</details>

#### gates Simple predicate promotion on candidate and safety facts

- gates Simple predicate promotion on candidate and safety facts
   - Expected: missing.recommendation_names does not contain `simple-predicate-promote`
   - Expected: found_missing_safety is true
   - Expected: medium.recommendation_names does not contain `simple-predicate-promote`
   - Expected: found_cost_skip is true
   - Expected: ready.recommendation_names contains `simple-predicate-promote`
   - Expected: llvm.recommendation_names does not contain `simple-predicate-promote`
   - Expected: found_llvm_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates Simple predicate promotion on candidate and safety facts")
val missing = backend_optimization_plan_for_budget_with_facts("cranelift", "high", ["typed_mir", "predication_candidate"])
expect(missing.recommendation_names.contains("simple-predicate-promote")).to_equal(false)
var found_missing_safety = false
for decision in missing.skipped_decisions:
    if decision.stable_name == "simple-predicate-promote" and decision.reason == "missing predicate_safe":
        found_missing_safety = true
expect(found_missing_safety).to_equal(true)

val medium = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "predication_candidate", "predicate_safe"])
expect(medium.recommendation_names.contains("simple-predicate-promote")).to_equal(false)
var found_cost_skip = false
for decision in medium.skipped_decisions:
    if decision.stable_name == "simple-predicate-promote" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)

val ready = backend_optimization_plan_for_budget_with_facts("cranelift", "high", ["typed_mir", "predication_candidate", "predicate_safe"])
expect(ready.recommendation_names.contains("simple-predicate-promote")).to_equal(true)

val llvm = backend_optimization_plan_for_budget_with_facts("llvm", "high", ["typed_mir", "predication_candidate", "predicate_safe", "llvm_backend_available"])
expect(llvm.recommendation_names.contains("simple-predicate-promote")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_decisions:
    if decision.stable_name == "simple-predicate-promote" and decision.reason == "llvm_runs_if_conversion_and_select_promotion":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>

#### gates Simple strength reduction on candidate and induction facts

- gates Simple strength reduction on candidate and induction facts
   - Expected: missing.recommendation_names does not contain `simple-strength-reduce`
   - Expected: found_missing_induction is true
   - Expected: low.recommendation_names does not contain `simple-strength-reduce`
   - Expected: found_cost_skip is true
   - Expected: ready.recommendation_names contains `simple-strength-reduce`
   - Expected: llvm.recommendation_names does not contain `simple-strength-reduce`
   - Expected: found_llvm_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates Simple strength reduction on candidate and induction facts")
val missing = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "strength_reduce_candidate"])
expect(missing.recommendation_names.contains("simple-strength-reduce")).to_equal(false)
var found_missing_induction = false
for decision in missing.skipped_decisions:
    if decision.stable_name == "simple-strength-reduce" and decision.reason == "missing induction_safe":
        found_missing_induction = true
expect(found_missing_induction).to_equal(true)

val low = backend_optimization_plan_for_budget_with_facts("cranelift", "low", ["typed_mir", "strength_reduce_candidate", "induction_safe"])
expect(low.recommendation_names.contains("simple-strength-reduce")).to_equal(false)
var found_cost_skip = false
for decision in low.skipped_decisions:
    if decision.stable_name == "simple-strength-reduce" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)

val ready = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "strength_reduce_candidate", "induction_safe"])
expect(ready.recommendation_names.contains("simple-strength-reduce")).to_equal(true)

val llvm = backend_optimization_plan_for_budget_with_facts("llvm", "medium", ["typed_mir", "strength_reduce_candidate", "induction_safe", "llvm_backend_available"])
expect(llvm.recommendation_names.contains("simple-strength-reduce")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_decisions:
    if decision.stable_name == "simple-strength-reduce" and decision.reason == "llvm_runs_scalar_strength_reduction":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>

#### gates Simple scalar cleanup on SSA and alias facts

- gates Simple scalar cleanup on SSA and alias facts
   - Expected: missing.recommendation_names does not contain `simple-scalar-cleanup`
   - Expected: found_missing_alias is true
   - Expected: low.recommendation_names does not contain `simple-scalar-cleanup`
   - Expected: found_cost_skip is true
   - Expected: ready.recommendation_names contains `simple-scalar-cleanup`
   - Expected: llvm.recommendation_names does not contain `simple-scalar-cleanup`
   - Expected: found_llvm_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates Simple scalar cleanup on SSA and alias facts")
val missing = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "ssa.canonical"])
expect(missing.recommendation_names.contains("simple-scalar-cleanup")).to_equal(false)
var found_missing_alias = false
for decision in missing.skipped_decisions:
    if decision.stable_name == "simple-scalar-cleanup" and decision.reason == "missing alias_stable":
        found_missing_alias = true
expect(found_missing_alias).to_equal(true)

val low = backend_optimization_plan_for_budget_with_facts("cranelift", "low", ["typed_mir", "ssa.canonical", "alias_stable"])
expect(low.recommendation_names.contains("simple-scalar-cleanup")).to_equal(false)
var found_cost_skip = false
for decision in low.skipped_decisions:
    if decision.stable_name == "simple-scalar-cleanup" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)

val ready = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "ssa.canonical", "alias_stable"])
expect(ready.recommendation_names.contains("simple-scalar-cleanup")).to_equal(true)

val llvm = backend_optimization_plan_for_budget_with_facts("llvm", "medium", ["typed_mir", "ssa.canonical", "alias_stable", "llvm_backend_available"])
expect(llvm.recommendation_names.contains("simple-scalar-cleanup")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_decisions:
    if decision.stable_name == "simple-scalar-cleanup" and decision.reason == "llvm_runs_gvn_and_scalar_cleanup":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>

#### keeps LLVM alloca shaping behind reassignment and backend facts

- keeps LLVM alloca shaping behind reassignment and backend facts
   - Expected: found_missing_var is true
   - Expected: found_missing_escape_analysis is true
   - Expected: ready.recommendation_names contains `llvm-entry-alloca-shaping`
   - Expected: ready.recommendation_names contains `llvm-default-pipeline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps LLVM alloca shaping behind reassignment and backend facts")
var found_missing_var = false
for decision in backend_optimization_decisions_for_budget_with_facts("llvm", "high", ["typed_mir", "llvm_backend_available"]):
    if decision.stable_name == "llvm-entry-alloca-shaping" and decision.reason == "missing var.reassignment":
        found_missing_var = true
expect(found_missing_var).to_equal(true)

var found_missing_escape_analysis = false
for decision in backend_optimization_decisions_for_budget_with_facts("llvm", "high", ["typed_mir", "var.reassignment", "escape.no_escape", "borrow.reassign_safe", "llvm_backend_available"]):
    if decision.stable_name == "llvm-entry-alloca-shaping" and decision.reason == "missing escape.analyzed":
        found_missing_escape_analysis = true
expect(found_missing_escape_analysis).to_equal(true)

val ready = backend_optimization_plan_for_budget_with_facts("llvm", "high", ["typed_mir", "var.reassignment", "escape.analyzed", "escape.no_escape", "borrow.reassign_safe", "llvm_backend_available"])
expect(ready.recommendation_names.contains("llvm-entry-alloca-shaping")).to_equal(true)
expect(ready.recommendation_names.contains("llvm-default-pipeline")).to_equal(true)
```

</details>

#### gates Simple auto-vectorization on candidate and alias facts

- gates Simple auto-vectorization on candidate and alias facts
   - Expected: missing.recommendation_names does not contain `simple-auto-vectorize`
   - Expected: found_missing_alias is true
   - Expected: medium.recommendation_names does not contain `simple-auto-vectorize`
   - Expected: found_cost_skip is true
   - Expected: ready.recommendation_names contains `simple-auto-vectorize`
   - Expected: llvm.recommendation_names does not contain `simple-auto-vectorize`
   - Expected: found_llvm_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates Simple auto-vectorization on candidate and alias facts")
val missing = backend_optimization_plan_for_budget_with_facts("cranelift", "high", ["typed_mir", "vectorization_candidate"])
expect(missing.recommendation_names.contains("simple-auto-vectorize")).to_equal(false)
var found_missing_alias = false
for decision in missing.skipped_decisions:
    if decision.stable_name == "simple-auto-vectorize" and decision.reason == "missing alias_stable":
        found_missing_alias = true
expect(found_missing_alias).to_equal(true)

val medium = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "vectorization_candidate", "alias_stable"])
expect(medium.recommendation_names.contains("simple-auto-vectorize")).to_equal(false)
var found_cost_skip = false
for decision in medium.skipped_decisions:
    if decision.stable_name == "simple-auto-vectorize" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)

val ready = backend_optimization_plan_for_budget_with_facts("cranelift", "high", ["typed_mir", "vectorization_candidate", "alias_stable"])
expect(ready.recommendation_names.contains("simple-auto-vectorize")).to_equal(true)

val llvm = backend_optimization_plan_for_budget_with_facts("llvm", "high", ["typed_mir", "vectorization_candidate", "alias_stable", "llvm_backend_available"])
expect(llvm.recommendation_names.contains("simple-auto-vectorize")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_decisions:
    if decision.stable_name == "simple-auto-vectorize" and decision.reason == "llvm_runs_vectorizer_pipeline":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>

#### gates Simple hot-call inlining on profile and budget facts

- gates Simple hot-call inlining on profile and budget facts
   - Expected: missing.recommendation_names does not contain `simple-hot-call-inline`
   - Expected: found_missing_budget is true
   - Expected: medium.recommendation_names does not contain `simple-hot-call-inline`
   - Expected: found_cost_skip is true
   - Expected: ready.recommendation_names contains `simple-hot-call-inline`
   - Expected: llvm.recommendation_names does not contain `simple-hot-call-inline`
   - Expected: found_llvm_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates Simple hot-call inlining on profile and budget facts")
val missing = backend_optimization_plan_for_budget_with_facts("cranelift", "high", ["typed_mir", "profile.hot_call"])
expect(missing.recommendation_names.contains("simple-hot-call-inline")).to_equal(false)
var found_missing_budget = false
for decision in missing.skipped_decisions:
    if decision.stable_name == "simple-hot-call-inline" and decision.reason == "missing inline_budget":
        found_missing_budget = true
expect(found_missing_budget).to_equal(true)

val medium = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["typed_mir", "profile.hot_call", "inline_budget"])
expect(medium.recommendation_names.contains("simple-hot-call-inline")).to_equal(false)
var found_cost_skip = false
for decision in medium.skipped_decisions:
    if decision.stable_name == "simple-hot-call-inline" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)

val ready = backend_optimization_plan_for_budget_with_facts("cranelift", "high", ["typed_mir", "profile.hot_call", "inline_budget"])
expect(ready.recommendation_names.contains("simple-hot-call-inline")).to_equal(true)

val llvm = backend_optimization_plan_for_budget_with_facts("llvm", "high", ["typed_mir", "profile.hot_call", "inline_budget", "llvm_backend_available"])
expect(llvm.recommendation_names.contains("simple-hot-call-inline")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_decisions:
    if decision.stable_name == "simple-hot-call-inline" and decision.reason == "llvm_runs_inliner_pipeline":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering general optimization backend recommendations for REQ-OPJH-022 REQ-OPJH-025 REQ-OPJH-026.
- general optimization backend recommendations for REQ-OPJH-022 REQ-OPJH-025 REQ-OPJH-026

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OPJH-022`
- `REQ-OPJH-025`
- `REQ-OPJH-026":`
- `REQ-OPJH-026`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b548bce884a9d78468a9c980ee0baa42c94c4be449315fb5cee1b5a7581e4c99`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b548bce884a9d78468a9c980ee0baa42c94c4be449315fb5cee1b5a7581e4c99`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b548bce884a9d78468a9c980ee0baa42c94c4be449315fb5cee1b5a7581e4c99`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl
mirror: doc/06_spec/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl:27:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps SSA var canonicalization for Cranelift hotspot planning' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips Simple-side SSA var canonicalization for LLVM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps high-level MIR optimizations for both Cranelift and LLVM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Simple-owned LICM away from LLVM default pipeline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
