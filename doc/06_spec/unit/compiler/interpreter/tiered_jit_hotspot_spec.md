# Tiered Jit Hotspot Specification

## Scenarios

### Tiered JIT hotspot facts

#### does not emit profile.hot_count below threshold

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_hotspot_profile_facts(hot_profile(7), hotspot_config(), true, true)
expect(facts.contains("profile.hot_count")).to_equal(false)
expect(facts.contains("typed_mir")).to_equal(true)
expect(facts.contains("safe_deopt")).to_equal(true)
```

</details>

#### emits optimizer facts for hot typed code with safe deopt

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_hotspot_profile_facts(hot_profile(8), hotspot_config(), true, true)
expect(facts.contains("profile.hot_count")).to_equal(true)
expect(facts.contains("typed_mir")).to_equal(true)
expect(facts.contains("safe_deopt")).to_equal(true)
```

</details>

#### creates an eligible plan only when all runtime facts exist

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = jit_hotspot_plan_from_profile(hot_profile(64), hotspot_config(), true, true)
expect(plan.function_name).to_equal("hot_loop")
expect(plan.eligible).to_equal(true)
expect(plan.invalidated).to_equal(false)
expect(plan.reason).to_equal("ready")
```

</details>

#### rejects missing safe deopt without losing profile facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = jit_hotspot_plan_from_profile(hot_profile(64), hotspot_config(), true, false)
expect(plan.eligible).to_equal(false)
expect(plan.reason).to_equal("missing safe_deopt")
expect(plan.facts.contains("profile.hot_count")).to_equal(true)
expect(plan.facts.contains("safe_deopt")).to_equal(false)
```

</details>

#### emits var optimization facts for SSA and borrow-safe reassignment

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 3, true, true, true, true)
val fact_list = jit_var_optimization_fact_list(facts)
expect(fact_list.contains("var.reassignment")).to_equal(true)
expect(fact_list.contains("ssa.var_transform")).to_equal(true)
expect(fact_list.contains("escape.analyzed")).to_equal(true)
expect(fact_list.contains("escape.no_escape")).to_equal(true)
expect(fact_list.contains("borrow.reassign_safe")).to_equal(true)
expect(jit_var_optimization_reason(facts)).to_equal("ready")
```

</details>

#### does not emit reassignment fact for zero reassignment count

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 0, true, true, true, true)
val fact_list = jit_var_optimization_fact_list(facts)
expect(fact_list.contains("var.reassignment")).to_equal(false)
expect(fact_list.contains("ssa.var_transform")).to_equal(true)
expect(jit_var_optimization_reason(facts)).to_equal("ready")
```

</details>

#### rejects var reassignment hotspot plans without SSA transform

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 2, false, true, true, true)
val plan = jit_hotspot_plan_with_var_facts(hot_profile(64), hotspot_config(), true, true, facts)
expect(plan.eligible).to_equal(false)
expect(plan.reason).to_equal("missing ssa.var_transform")
expect(plan.facts.contains("var.reassignment")).to_equal(true)
```

</details>

#### rejects var reassignment hotspot plans when reassigned storage may escape

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 2, true, true, false, true)
val plan = jit_hotspot_plan_with_var_facts(hot_profile(64), hotspot_config(), true, true, facts)
expect(plan.eligible).to_equal(false)
expect(plan.reason).to_equal("missing escape.no_escape")
expect(plan.facts.contains("escape.analyzed")).to_equal(true)
```

</details>

#### rejects var reassignment hotspot plans without borrow reassignment safety

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 2, true, true, true, false)
val plan = jit_hotspot_plan_with_var_facts(hot_profile(64), hotspot_config(), true, true, facts)
expect(plan.eligible).to_equal(false)
expect(plan.reason).to_equal("missing borrow.reassign_safe")
```

</details>

#### accepts var reassignment hotspot plans only after SSA, escape, and borrow facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 2, true, true, true, true)
val plan = jit_hotspot_plan_with_var_facts(hot_profile(64), hotspot_config(), true, true, facts)
expect(plan.eligible).to_equal(true)
expect(plan.reason).to_equal("ready")
expect(plan.facts.contains("profile.hot_count")).to_equal(true)
expect(plan.facts.contains("ssa.var_transform")).to_equal(true)
expect(plan.facts.contains("escape.analyzed")).to_equal(true)
expect(plan.facts.contains("borrow.reassign_safe")).to_equal(true)
```

</details>

#### uses stored FunctionProfile var facts for manager-style hotspot planning

1. source: "fn hot loop

2. var facts: jit var optimization facts
   - Expected: plan.eligible is false
   - Expected: plan.reason equals `missing escape.no_escape`
   - Expected: plan.facts contains `var.reassignment`
   - Expected: plan.facts does not contain `escape.no_escape`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = FunctionProfile(
    name: "hot_loop",
    call_count: 64,
    tier: JitTier.Interpreted,
    compile_time_ms: 0.0,
    source: "fn hot_loop(x: i64) -> i64: x + 1",
    typed_mir: true,
    safe_deopt: true,
    hotspot_specialized_source: "",
    hotspot_semantic_proof: false,
    var_facts: jit_var_optimization_facts(true, 2, true, true, false, true)
)
val plan = jit_hotspot_plan_from_profile_var_facts(profile, hotspot_config(), true, true)
expect(plan.eligible).to_equal(false)
expect(plan.reason).to_equal("missing escape.no_escape")
expect(plan.facts.contains("var.reassignment")).to_equal(true)
expect(plan.facts.contains("escape.no_escape")).to_equal(false)
```

</details>

#### rejects hotspot rebuild choices when reassigned var storage may escape

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 2, true, true, false, true)
val plan = jit_hotspot_rebuild_choice(hot_profile_with_var_facts(256, facts), hotspot_config(), true, true, "high")
expect(plan.eligible).to_equal(false)
expect(plan.selected_backend).to_equal("")
expect(plan.reason).to_equal("missing escape.no_escape")
expect(plan.attempted_backends.len()).to_equal(0)
```

</details>

#### rejects optimization passes and plugins for unsafe var rebuild facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 2, true, true, false, true)
val plan = jit_hotspot_optimization_plan(hot_profile_with_var_facts(256, facts), hotspot_config(), true, true, "high")
expect(plan.eligible).to_equal(false)
expect(plan.backend).to_equal("")
expect(plan.reason).to_equal("missing escape.no_escape")
expect(plan.passes.len()).to_equal(0)
expect(plan.plugin_recommendations.len()).to_equal(0)
```

</details>

#### keeps backend rebuild selection eligible for SSA escape-safe var reassignment

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 2, true, true, true, true)
val plan = jit_hotspot_rebuild_choice(hot_profile_with_var_facts(256, facts), hotspot_config(), true, true, "high")
expect(plan.eligible).to_equal(true)
expect(plan.selected_backend).to_equal("llvm")
expect(plan.reason).to_equal("ready")
```

</details>

#### plans Cranelift hotspot rebuilds at tier1 cost

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = jit_hotspot_rebuild_plan(hot_profile(8), hotspot_config(), "cranlift", true)
expect(plan.backend).to_equal("cranelift")
expect(plan.eligible).to_equal(true)
expect(plan.cost_class).to_equal("medium")
expect(plan.required_count).to_equal(8)
```

</details>

#### defers LLVM hotspot rebuilds until tier2 because compile cost is high

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = jit_hotspot_rebuild_plan(hot_profile(64), hotspot_config(), "llvm", true)
expect(plan.backend).to_equal("llvm")
expect(plan.eligible).to_equal(false)
expect(plan.reason).to_equal("missing tier2 hot_count")
expect(plan.cost_class).to_equal("high")
expect(plan.required_count).to_equal(128)
```

</details>

#### accepts LLVM hotspot rebuilds at tier2 only when the backend is available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unavailable = jit_hotspot_rebuild_plan(hot_profile(256), hotspot_config(), "llvm", false)
expect(unavailable.eligible).to_equal(false)
expect(unavailable.reason).to_equal("backend unavailable")
val ready = jit_hotspot_rebuild_plan(hot_profile(256), hotspot_config(), "llvm", true)
expect(ready.eligible).to_equal(true)
expect(ready.reason).to_equal("ready")
expect(jit_hotspot_rebuild_backend_name("cranlift")).to_equal("cranelift")
```

</details>

#### normalizes llvm-lib to the LLVM rebuild policy

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = jit_hotspot_rebuild_plan(hot_profile(256), hotspot_config(), "llvm-lib", true)
expect(ready.backend).to_equal("llvm")
expect(ready.cost_class).to_equal("high")
expect(jit_hotspot_rebuild_backend_name("llvmlib")).to_equal("llvm")
```

</details>

#### rejects LLVM rebuilds when compile cost budget is below high

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = jit_hotspot_rebuild_plan_with_cost_budget(hot_profile(256), hotspot_config(), "llvm", true, "medium")
expect(plan.eligible).to_equal(false)
expect(plan.reason).to_equal("cost budget exceeded")
expect(plan.cost_class).to_equal("high")
expect(jit_hotspot_cost_allowed("medium", "medium")).to_equal(true)
expect(jit_hotspot_cost_allowed("high", "medium")).to_equal(false)
```

</details>

#### selects Cranelift for tier1 heat and LLVM only for tier2 heat

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tier1 = jit_hotspot_rebuild_choice(hot_profile(64), hotspot_config(), true, true, "high")
expect(tier1.eligible).to_equal(true)
expect(tier1.selected_backend).to_equal("cranelift")
expect(tier1.required_count).to_equal(8)

val tier2 = jit_hotspot_rebuild_choice(hot_profile(256), hotspot_config(), true, true, "high")
expect(tier2.eligible).to_equal(true)
expect(tier2.selected_backend).to_equal("llvm")
expect(tier2.required_count).to_equal(128)
```

</details>

#### keeps barely tier2-hot functions on Cranelift when both backends are available

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val barely_tier2 = jit_hotspot_rebuild_choice(hot_profile(128), hotspot_config(), true, true, "high")
expect(barely_tier2.eligible).to_equal(true)
expect(barely_tier2.selected_backend).to_equal("cranelift")
expect(barely_tier2.cost_class).to_equal("medium")

val llvm_only = jit_hotspot_rebuild_choice(hot_profile(128), hotspot_config(), false, true, "high")
expect(llvm_only.eligible).to_equal(true)
expect(llvm_only.selected_backend).to_equal("llvm")
expect(llvm_only.cost_class).to_equal("high")
```

</details>

#### falls back to Cranelift when LLVM is too expensive or unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val budgeted = jit_hotspot_rebuild_choice(hot_profile(256), hotspot_config(), true, true, "medium")
expect(budgeted.eligible).to_equal(true)
expect(budgeted.selected_backend).to_equal("cranelift")
expect(budgeted.cost_class).to_equal("medium")

val unavailable = jit_hotspot_rebuild_choice(hot_profile(256), hotspot_config(), true, false, "high")
expect(unavailable.eligible).to_equal(true)
expect(unavailable.selected_backend).to_equal("cranelift")
```

</details>

#### builds Cranelift hotspot optimization plans with medium-cost local passes

<details>
<summary>Executable SPipe</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = jit_hotspot_optimization_plan(hot_profile(256), hotspot_config(), true, true, "medium")
expect(plan.eligible).to_equal(true)
expect(plan.backend).to_equal("cranelift")
expect(plan.max_cost_class).to_equal("medium")
expect(plan.opt_level).to_equal("aggressive")
expect(plan.passes.contains("dead_code_elimination")).to_equal(true)
expect(plan.passes.contains("loop_unroll")).to_equal(true)
expect(plan.passes.contains("inline_aggressive")).to_equal(false)
expect(plan.passes.contains("auto_vectorize")).to_equal(false)
expect(plan.plugin_recommendations.contains("early-dead-code-prune")).to_equal(true)
expect(plan.plugin_recommendations.contains("ssa-var-canon")).to_equal(false)
expect(plan.plugin_recommendations.contains("cranelift-local-licm")).to_equal(false)
expect(plan.plugin_recommendations.contains("llvm-entry-alloca-shaping")).to_equal(false)
var found_cost_skip = false
for decision in plan.skipped_passes:
    if decision.pass_name == "inline_aggressive" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)
var found_llvm_plugin_skip = false
var found_missing_ssa = false
for decision in plan.skipped_plugin_recommendations:
    if decision.stable_name == "llvm-entry-alloca-shaping" and decision.reason == "llvm_frontend_alloca_promotion_shape":
        found_llvm_plugin_skip = true
    if decision.stable_name == "ssa-var-canon" and decision.reason == "missing ssa.var_transform":
        found_missing_ssa = true
expect(found_llvm_plugin_skip).to_equal(true)
expect(found_missing_ssa).to_equal(true)
```

</details>

#### builds LLVM hotspot optimization plans without Simple passes LLVM already owns

<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = jit_hotspot_optimization_plan(hot_profile(256), hotspot_config(), true, true, "high")
expect(plan.eligible).to_equal(true)
expect(plan.backend).to_equal("llvm")
expect(plan.cost_class).to_equal("high")
expect(plan.passes.contains("dead_code_elimination")).to_equal(true)
expect(plan.passes.contains("inline_aggressive")).to_equal(false)
expect(plan.passes.contains("auto_vectorize")).to_equal(false)
expect(plan.passes.contains("strength_reduction")).to_equal(false)
expect(plan.passes.contains("loop_unroll")).to_equal(false)
expect(plan.passes.contains("predicate_promote")).to_equal(false)
expect(plan.plugin_recommendations.contains("llvm-entry-alloca-shaping")).to_equal(false)
expect(plan.plugin_recommendations.contains("llvm-default-pipeline")).to_equal(true)
expect(plan.plugin_recommendations.contains("ssa-var-canon")).to_equal(false)
expect(plan.plugin_recommendations.contains("cranelift-local-licm")).to_equal(false)
var found_llvm_skip = false
for decision in plan.skipped_passes:
    if decision.pass_name == "auto_vectorize" and decision.reason == "llvm_runs_vectorizer_pipeline":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
var found_llvm_owned_plugin_skip = false
var found_missing_var = false
for decision in plan.skipped_plugin_recommendations:
    if decision.stable_name == "ssa-var-canon" and decision.reason == "llvm_backend_runs_mem2reg_sroa_pipeline":
        found_llvm_owned_plugin_skip = true
    if decision.stable_name == "llvm-entry-alloca-shaping" and decision.reason == "missing var.reassignment":
        found_missing_var = true
expect(found_llvm_owned_plugin_skip).to_equal(true)
expect(found_missing_var).to_equal(true)
```

</details>

#### adds var-specific plugin recommendations only when hotspot facts prove them

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 2, true, true, true, true)
val cranelift = jit_hotspot_optimization_plan(hot_profile_with_var_facts(256, facts), hotspot_config(), true, true, "medium")
expect(cranelift.plugin_recommendations.contains("ssa-var-canon")).to_equal(true)
expect(cranelift.plugin_recommendations.contains("simple-scalar-cleanup")).to_equal(true)
expect(cranelift.plugin_recommendations.contains("cranelift-local-licm")).to_equal(false)

val llvm = jit_hotspot_optimization_plan(hot_profile_with_var_facts(256, facts), hotspot_config(), true, true, "high")
expect(llvm.plugin_recommendations.contains("llvm-entry-alloca-shaping")).to_equal(true)
expect(llvm.plugin_recommendations.contains("ssa-var-canon")).to_equal(false)
expect(llvm.plugin_recommendations.contains("simple-scalar-cleanup")).to_equal(false)
```

</details>

#### does not derive var cleanup recommendations without actual reassignment

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(false, 0, true, true, true, true)
val cranelift = jit_hotspot_optimization_plan(hot_profile_with_var_facts(256, facts), hotspot_config(), true, true, "medium")
expect(cranelift.plugin_recommendations.contains("ssa-var-canon")).to_equal(false)
expect(cranelift.plugin_recommendations.contains("simple-scalar-cleanup")).to_equal(false)
var found_missing_reassignment = false
var found_missing_canonical = false
for decision in cranelift.skipped_plugin_recommendations:
    if decision.stable_name == "ssa-var-canon" and decision.reason == "missing var.reassignment":
        found_missing_reassignment = true
    if decision.stable_name == "simple-scalar-cleanup" and decision.reason == "missing ssa.canonical":
        found_missing_canonical = true
expect(found_missing_reassignment).to_equal(true)
expect(found_missing_canonical).to_equal(true)
```

</details>

<details>
<summary>Advanced: adds LICM recommendations only when structured loops also have alias-stable facts</summary>

#### adds LICM recommendations only when structured loops also have alias-stable facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = jit_var_optimization_facts(true, 2, true, true, true, true)
val cranelift = jit_hotspot_optimization_plan(hot_structured_loop_with_var_facts(256, facts), hotspot_config(), true, true, "medium")
expect(cranelift.backend).to_equal("cranelift")
expect(cranelift.plugin_recommendations.contains("cranelift-local-licm")).to_equal(true)
expect(cranelift.plugin_recommendations.contains("simple-loop-unroll")).to_equal(false)

val llvm = jit_hotspot_optimization_plan(hot_structured_loop_with_var_facts(256, facts), hotspot_config(), true, true, "high")
expect(llvm.backend).to_equal("llvm")
expect(llvm.plugin_recommendations.contains("cranelift-local-licm")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_plugin_recommendations:
    if decision.stable_name == "cranelift-local-licm" and decision.reason == "llvm_default_pipeline_runs_loop_optimizations":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: adds loop-unroll recommendations only for small fixed-trip loops</summary>

#### adds loop-unroll recommendations only for small fixed-trip loops

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cranelift = jit_hotspot_optimization_plan(hot_fixed_trip_loop_profile(256), hotspot_config(), true, true, "medium")
expect(cranelift.backend).to_equal("cranelift")
expect(cranelift.plugin_recommendations.contains("simple-loop-unroll")).to_equal(true)

val llvm = jit_hotspot_optimization_plan(hot_fixed_trip_loop_profile(256), hotspot_config(), true, true, "high")
expect(llvm.backend).to_equal("llvm")
expect(llvm.plugin_recommendations.contains("simple-loop-unroll")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_plugin_recommendations:
    if decision.stable_name == "simple-loop-unroll" and decision.reason == "llvm_runs_loop_unroll_pipeline":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>


</details>

#### adds predicate promotion recommendations only for safe branch-select facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cranelift = jit_hotspot_optimization_plan(hot_predicate_profile(256), hotspot_config(), true, true, "high")
expect(cranelift.backend).to_equal("cranelift")
expect(cranelift.plugin_recommendations.contains("simple-predicate-promote")).to_equal(true)

val medium = jit_hotspot_optimization_plan(hot_predicate_profile(256), hotspot_config(), true, true, "medium")
expect(medium.plugin_recommendations.contains("simple-predicate-promote")).to_equal(false)
var found_cost_skip = false
for decision in medium.skipped_plugin_recommendations:
    if decision.stable_name == "simple-predicate-promote" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)

val llvm = jit_hotspot_optimization_plan(hot_predicate_profile(256), hotspot_config(), true, true, "high")
expect(llvm.backend).to_equal("llvm")
expect(llvm.plugin_recommendations.contains("simple-predicate-promote")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_plugin_recommendations:
    if decision.stable_name == "simple-predicate-promote" and decision.reason == "llvm_runs_if_conversion_and_select_promotion":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>

<details>
<summary>Advanced: adds vectorization recommendations only when indexed loop facts are alias-stable</summary>

#### adds vectorization recommendations only when indexed loop facts are alias-stable

<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_alias_facts = jit_var_optimization_facts_none()
val missing_alias = jit_hotspot_optimization_plan(hot_vector_loop_with_var_facts(256, no_alias_facts), hotspot_config(), true, true, "high")
expect(missing_alias.plugin_recommendations.contains("simple-auto-vectorize")).to_equal(false)
var found_missing_alias = false
for decision in missing_alias.skipped_plugin_recommendations:
    if decision.stable_name == "simple-auto-vectorize" and decision.reason == "missing alias_stable":
        found_missing_alias = true
expect(found_missing_alias).to_equal(true)

val facts = jit_var_optimization_facts(true, 2, true, true, true, true)
val cranelift = jit_hotspot_optimization_plan(hot_vector_loop_with_var_facts(256, facts), hotspot_config(), true, true, "high")
expect(cranelift.backend).to_equal("cranelift")
expect(cranelift.plugin_recommendations.contains("simple-auto-vectorize")).to_equal(true)

val llvm = jit_hotspot_optimization_plan(hot_vector_loop_with_var_facts(256, facts), hotspot_config(), true, true, "high")
expect(llvm.backend).to_equal("llvm")
expect(llvm.plugin_recommendations.contains("simple-auto-vectorize")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_plugin_recommendations:
    if decision.stable_name == "simple-auto-vectorize" and decision.reason == "llvm_runs_vectorizer_pipeline":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: adds bounds-check elimination recommendations when indexed loops expose range facts</summary>

#### adds bounds-check elimination recommendations when indexed loops expose range facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cranelift = jit_hotspot_optimization_plan(hot_range_loop_profile(256), hotspot_config(), true, true, "medium")
expect(cranelift.backend).to_equal("cranelift")
expect(cranelift.plugin_recommendations.contains("bounds-check-elim")).to_equal(true)

val low = jit_hotspot_optimization_plan(hot_range_loop_profile(256), hotspot_config(), true, true, "low")
expect(low.plugin_recommendations.contains("bounds-check-elim")).to_equal(false)
var found_cost_skip = false
for decision in low.skipped_plugin_recommendations:
    if decision.stable_name == "bounds-check-elim" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)

val llvm = jit_hotspot_optimization_plan(hot_range_loop_profile(256), hotspot_config(), true, true, "high")
expect(llvm.backend).to_equal("llvm")
expect(llvm.plugin_recommendations.contains("bounds-check-elim")).to_equal(true)
```

</details>


</details>

#### adds hot-call inline recommendations only for high-budget non-LLVM direct calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cranelift = jit_hotspot_optimization_plan(hot_direct_call_profile(256), hotspot_config(), true, true, "high")
expect(cranelift.backend).to_equal("cranelift")
expect(cranelift.plugin_recommendations.contains("simple-hot-call-inline")).to_equal(true)

val medium = jit_hotspot_optimization_plan(hot_direct_call_profile(256), hotspot_config(), true, true, "medium")
expect(medium.plugin_recommendations.contains("simple-hot-call-inline")).to_equal(false)
var found_cost_skip = false
for decision in medium.skipped_plugin_recommendations:
    if decision.stable_name == "simple-hot-call-inline" and decision.reason == "cost budget exceeded":
        found_cost_skip = true
expect(found_cost_skip).to_equal(true)

val llvm = jit_hotspot_optimization_plan(hot_direct_call_profile(256), hotspot_config(), true, true, "high")
expect(llvm.backend).to_equal("llvm")
expect(llvm.plugin_recommendations.contains("simple-hot-call-inline")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_plugin_recommendations:
    if decision.stable_name == "simple-hot-call-inline" and decision.reason == "llvm_runs_inliner_pipeline":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>

#### adds strength-reduction plugin recommendations only for low-tier eligible source facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cranelift = jit_hotspot_optimization_plan(hot_strength_profile(256), hotspot_config(), true, true, "medium")
expect(cranelift.backend).to_equal("cranelift")
expect(cranelift.plugin_recommendations.contains("simple-strength-reduce")).to_equal(true)

val llvm = jit_hotspot_optimization_plan(hot_strength_profile(256), hotspot_config(), true, true, "high")
expect(llvm.backend).to_equal("llvm")
expect(llvm.plugin_recommendations.contains("simple-strength-reduce")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_plugin_recommendations:
    if decision.stable_name == "simple-strength-reduce" and decision.reason == "llvm_runs_scalar_strength_reduction":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>

#### adds byte-scan plugin recommendations for bounded scan source facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cranelift = jit_hotspot_optimization_plan(hot_byte_scan_profile(256), hotspot_config(), true, true, "medium")
expect(cranelift.backend).to_equal("cranelift")
expect(cranelift.plugin_recommendations.contains("byte-scan-to-delimiter")).to_equal(true)

val llvm = jit_hotspot_optimization_plan(hot_byte_scan_profile(256), hotspot_config(), true, true, "high")
expect(llvm.backend).to_equal("llvm")
expect(llvm.plugin_recommendations.contains("byte-scan-to-delimiter")).to_equal(true)
```

</details>

#### adds checksum reducer recommendations for associative indexed reductions

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cranelift = jit_hotspot_optimization_plan(hot_checksum_profile(256), hotspot_config(), true, true, "medium")
expect(cranelift.backend).to_equal("cranelift")
expect(cranelift.plugin_recommendations.contains("checksum-reducer")).to_equal(true)

val llvm = jit_hotspot_optimization_plan(hot_checksum_profile(256), hotspot_config(), true, true, "high")
expect(llvm.backend).to_equal("llvm")
expect(llvm.plugin_recommendations.contains("checksum-reducer")).to_equal(true)
```

</details>

#### adds strength-reduction plugin recommendations only for low-tier eligible source facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cranelift = jit_hotspot_optimization_plan(hot_strength_profile(256), hotspot_config(), true, true, "medium")
expect(cranelift.backend).to_equal("cranelift")
expect(cranelift.plugin_recommendations.contains("simple-strength-reduce")).to_equal(true)

val llvm = jit_hotspot_optimization_plan(hot_strength_profile(256), hotspot_config(), true, true, "high")
expect(llvm.backend).to_equal("llvm")
expect(llvm.plugin_recommendations.contains("simple-strength-reduce")).to_equal(false)
var found_llvm_skip = false
for decision in llvm.skipped_plugin_recommendations:
    if decision.stable_name == "simple-strength-reduce" and decision.reason == "llvm_runs_scalar_strength_reduction":
        found_llvm_skip = true
expect(found_llvm_skip).to_equal(true)
```

</details>

#### keeps hotspot optimization plans consistent with shared backend budget planners

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hotspot = jit_hotspot_optimization_plan(hot_profile(256), hotspot_config(), true, true, "medium")
val mir_plan = optimizationpipeline_backend_plan_for_budget(OptLevel.Aggressive, "cranelift", "medium")
val plugin_plan = backend_optimization_plan_for_budget_with_facts("cranelift", "medium", ["profile.hot_count", "typed_mir", "safe_deopt", "cranelift_backend_available"])
expect(hotspot.passes).to_equal(mir_plan.passes)
expect(hotspot.skipped_passes.len()).to_equal(mir_plan.skipped_passes.len())
expect(hotspot.plugin_recommendations).to_equal(plugin_plan.recommendation_names)
expect(hotspot.skipped_plugin_recommendations.len()).to_equal(plugin_plan.skipped_decisions.len())
```

</details>

#### keeps LLVM hotspot optimization plans consistent with shared backend budget planners

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hotspot = jit_hotspot_optimization_plan(hot_profile(256), hotspot_config(), true, true, "high")
val mir_plan = optimizationpipeline_backend_plan_for_budget(OptLevel.Aggressive, "llvm", "high")
val plugin_plan = backend_optimization_plan_for_budget_with_facts("llvm", "high", ["profile.hot_count", "typed_mir", "safe_deopt", "llvm_backend_available"])
expect(hotspot.passes).to_equal(mir_plan.passes)
expect(hotspot.skipped_passes.len()).to_equal(mir_plan.skipped_passes.len())
expect(hotspot.plugin_recommendations).to_equal(plugin_plan.recommendation_names)
expect(hotspot.skipped_plugin_recommendations.len()).to_equal(plugin_plan.skipped_decisions.len())
```

</details>

#### does not create optimization passes for ineligible hotspot rebuilds

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = jit_hotspot_optimization_plan(hot_profile(2), hotspot_config(), true, true, "high")
expect(plan.eligible).to_equal(false)
expect(plan.reason).to_equal("missing tier1 hot_count")
expect(plan.passes.len()).to_equal(0)
expect(plan.skipped_passes.len()).to_equal(0)
expect(plan.plugin_recommendations.len()).to_equal(0)
expect(plan.skipped_plugin_recommendations.len()).to_equal(0)
```

</details>

#### rejects rebuilds when no backend can satisfy heat and cost policy

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cold = jit_hotspot_rebuild_choice(hot_profile(2), hotspot_config(), true, true, "high")
expect(cold.eligible).to_equal(false)
expect(cold.reason).to_equal("missing tier1 hot_count")

val unavailable = jit_hotspot_rebuild_choice(hot_profile(256), hotspot_config(), false, false, "high")
expect(unavailable.eligible).to_equal(false)
expect(unavailable.reason).to_equal("no backend available")
```

</details>

#### invalidates an existing hotspot plan explicitly

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = jit_hotspot_plan_from_profile(hot_profile(64), hotspot_config(), true, true)
val invalidated = jit_hotspot_plan_invalidate(plan, "guard changed")
expect(invalidated.eligible).to_equal(false)
expect(invalidated.invalidated).to_equal(true)
expect(invalidated.reason).to_equal("guard changed")
```

</details>

#### consumes eligible plans without changing fallback source

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hot_loop(x: i64) -> i64: x + 1"
val plan = jit_hotspot_plan_from_profile(hot_profile(64), hotspot_config(), true, true)
val decision = jit_hotspot_consume_plan(plan, source, true)
expect(decision.provider_used).to_equal(true)
expect(decision.compile_source).to_equal(source)
expect(decision.reason).to_equal("jit.hotspot_plan accepted")
```

</details>

#### does not consume plans when provider is disabled

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hot_loop(x: i64) -> i64: x + 1"
val plan = jit_hotspot_plan_from_profile(hot_profile(64), hotspot_config(), true, true)
val decision = jit_hotspot_consume_plan(plan, source, false)
expect(decision.provider_used).to_equal(false)
expect(decision.compile_source).to_equal(source)
expect(decision.reason).to_equal("provider disabled")
```

</details>

#### uses specialized source only with semantic proof

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hot_loop(x: i64) -> i64: x + 1"
val specialized = "fn hot_loop(x: i64) -> i64: x + 1 # specialized"
val plan = jit_hotspot_plan_from_profile(hot_profile(64), hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider("test.hotspot", specialized, true)
val decision = jit_hotspot_consume_plan_with_provider(plan, source, provider)
expect(decision.provider_used).to_equal(true)
expect(decision.compile_source).to_equal(specialized)
expect(decision.reason).to_equal("jit.hotspot_specialized_source accepted")
```

</details>

#### rejects specialized source without semantic proof

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hot_loop(x: i64) -> i64: x + 1"
val specialized = "fn hot_loop(x: i64) -> i64: x + 1 # specialized"
val plan = jit_hotspot_plan_from_profile(hot_profile(64), hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider("test.hotspot", specialized, false)
val decision = jit_hotspot_consume_plan_with_provider(plan, source, provider)
expect(decision.provider_used).to_equal(false)
expect(decision.compile_source).to_equal(source)
expect(decision.reason).to_equal("missing semantic proof")
```

</details>

#### derives semantic proof for specialization providers from analysis facts

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hot_loop(x: i64) -> i64: x + 1"
val specialized = "fn hot_loop(x: i64) -> i64: x + 1 # specialized"
val facts = [
    "typed_mir",
    "safe_deopt",
    "ssa.var_transform",
    "escape.analyzed",
    "escape.no_escape",
    "borrow.reassign_safe"
]
expect(jit_hotspot_analysis_has_semantic_proof(facts)).to_equal(true)
val plan = jit_hotspot_plan_from_profile(hot_profile(64), hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider_from_analysis("test.hotspot.analysis", specialized, facts)
val decision = jit_hotspot_consume_plan_with_provider(plan, source, provider)
expect(decision.provider_used).to_equal(true)
expect(decision.compile_source).to_equal(specialized)
```

</details>

#### rejects analysis-derived specialization when proof facts are incomplete

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hot_loop(x: i64) -> i64: x + 1"
val specialized = "fn hot_loop(x: i64) -> i64: x + 1 # specialized"
val facts = ["typed_mir", "safe_deopt", "ssa.var_transform", "escape.analyzed", "borrow.reassign_safe"]
expect(jit_hotspot_analysis_has_semantic_proof(facts)).to_equal(false)
val plan = jit_hotspot_plan_from_profile(hot_profile(64), hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider_from_analysis("test.hotspot.analysis", specialized, facts)
val decision = jit_hotspot_consume_plan_with_provider(plan, source, provider)
expect(decision.provider_used).to_equal(false)
expect(decision.compile_source).to_equal(source)
expect(decision.reason).to_equal("missing semantic proof")
```

</details>

#### connects profile analysis facts to a specialization provider

1. hotspot config
   - Expected: plan.eligible is true
   - Expected: decision.provider_used is true
   - Expected: decision.compile_source equals `specialized`


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hot_loop(x: i64) -> i64: x + 1"
val specialized = "fn hot_loop(x: i64) -> i64: x + 1 # specialized"
val facts = jit_var_optimization_facts(true, 2, true, true, true, true)
val profile = hot_profile_with_analysis_specialization(64, specialized, facts)
val plan = jit_hotspot_plan_from_profile_var_facts(profile, hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider_from_profile_analysis(
    "test.hotspot.profile.analysis",
    profile,
    hotspot_config(),
    true,
    true
)
val decision = jit_hotspot_consume_plan_with_provider(plan, source, provider)
expect(plan.eligible).to_equal(true)
expect(decision.provider_used).to_equal(true)
expect(decision.compile_source).to_equal(specialized)
```

</details>

#### keeps profile analysis specialization disabled when escape proof is missing

1. hotspot config
   - Expected: plan.eligible is false
   - Expected: plan.reason equals `missing escape.no_escape`
   - Expected: decision.provider_used is false
   - Expected: decision.compile_source equals `source`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hot_loop(x: i64) -> i64: x + 1"
val specialized = "fn hot_loop(x: i64) -> i64: x + 1 # specialized"
val facts = jit_var_optimization_facts(true, 2, true, true, false, true)
val profile = hot_profile_with_analysis_specialization(64, specialized, facts)
val plan = jit_hotspot_plan_from_profile_var_facts(profile, hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider_from_profile_analysis(
    "test.hotspot.profile.analysis",
    profile,
    hotspot_config(),
    true,
    true
)
val decision = jit_hotspot_consume_plan_with_provider(plan, source, provider)
expect(plan.eligible).to_equal(false)
expect(plan.reason).to_equal("missing escape.no_escape")
expect(decision.provider_used).to_equal(false)
expect(decision.compile_source).to_equal(source)
```

</details>

#### rejects missing specialized source

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hot_loop(x: i64) -> i64: x + 1"
val plan = jit_hotspot_plan_from_profile(hot_profile(64), hotspot_config(), true, true)
val provider = jit_hotspot_specialization_provider("test.hotspot", "", true)
val decision = jit_hotspot_consume_plan_with_provider(plan, source, provider)
expect(decision.provider_used).to_equal(false)
expect(decision.compile_source).to_equal(source)
expect(decision.reason).to_equal("missing specialized source")
```

</details>

#### does not allow manager compilation for ineligible var-hotspot plans

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn hot_loop(x: i64) -> i64: x + 1"
val facts = jit_var_optimization_facts(true, 2, true, true, false, true)
val plan = jit_hotspot_plan_with_var_facts(hot_profile(64), hotspot_config(), true, true, facts)
val provider = jit_hotspot_specialization_provider("test.hotspot", "", true)
val decision = jit_hotspot_consume_plan_with_provider(plan, source, provider)
expect(plan.eligible).to_equal(false)
expect(decision.compile_source).to_equal(source)
expect(jit_hotspot_compile_decision_allows_compile(decision)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tiered JIT hotspot facts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
