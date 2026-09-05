# Optimizer Manifest Backend Budget Specification

> <details>

<!-- sdn-diagram:id=optimizer_manifest_backend_budget_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=optimizer_manifest_backend_budget_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

optimizer_manifest_backend_budget_spec -> std
optimizer_manifest_backend_budget_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=optimizer_manifest_backend_budget_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimizer Manifest Backend Budget Specification

## Scenarios

### optimizer manifest backend and cost budget policy

#### defaults manifest-created passes to all backends and medium cost

- ManifestPassContract
   - Expected: manifest_result.? is true
   - Expected: registry_result.? is true
   - Expected: dynamic_pass_registry_names_for_backend(registry, "cranlift") contains `budget_default_pass`
   - Expected: dynamic_pass_registry_names_for_backend_budget(registry, "llvm-lib", "medium") contains `budget_default_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = manifest_pass_entry_new(
    "budget_default_pass",
    [],
    PassScope.Function,
    [],
    ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure"),
    "budget_default_pass_entry"
)
val manifest_result = load_manifest_v1_from_parsed(
    1,
    "simple.opt.mir.v1",
    "budget_default_plugin",
    "1.0.0",
    "0.9.0",
    [entry]
)
expect(manifest_result.?).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result.?).to_equal(true)

val registry = registry_result.unwrap()
expect(dynamic_pass_registry_names_for_backend(registry, "cranlift").contains("budget_default_pass")).to_equal(true)
expect(dynamic_pass_registry_names_for_backend_budget(registry, "llvm-lib", "medium").contains("budget_default_pass")).to_equal(true)
```

</details>

#### loads backend policy and cost class from JSON manifests

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"schema_version\":1,\"compiler_abi\":\"simple.opt.mir.v1\",\"name\":\"json_budget_plugin\",\"version\":\"1.0.0\",\"min_compiler_version\":\"0.9.0\",\"passes\":[{\"stable_name\":\"json_high_llvm_pass\",\"aliases\":[\"json_llvm_alias\"],\"scope\":\"function\",\"capability_requires\":[\"typed_mir\"],\"contract\":{\"inputs\":[\"typed_mir\"],\"outputs\":[\"canonical_mir\"],\"purity\":\"pure\"},\"backend_policy\":{\"only\":[\"llvm\"],\"reason\":\"json_llvm_only\"},\"cost_class\":\"high\",\"entry_symbol\":\"json_high_llvm_pass_entry\"}]}"
val manifest_result = load_manifest_v1(json)
expect(manifest_result.?).to_equal(true)
val manifest = manifest_result.unwrap()
expect(manifest.name).to_equal("json_budget_plugin")
expect(manifest.passes.len()).to_equal(1)
expect(manifest.passes[0].cost_class).to_equal("high")

val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest)
expect(registry_result.?).to_equal(true)
val registry = registry_result.unwrap()
expect(dynamic_pass_registry_names_for_backend_budget(registry, "llvm-lib", "medium").contains("json_high_llvm_pass")).to_equal(false)
expect(dynamic_pass_registry_names_for_backend_budget(registry, "llvm", "high").contains("json_high_llvm_pass")).to_equal(true)
expect(dynamic_pass_registry_names_for_backend_budget(registry, "cranelift", "high").contains("json_high_llvm_pass")).to_equal(false)
```

</details>

#### skips high-cost LLVM-only dynamic plugins under a medium budget

- ManifestPassContract
- optimization backend policy only
- ManifestPassContract
- optimization backend policy only
   - Expected: manifest_result.? is true
   - Expected: registry_result.? is true
   - Expected: manifest_cost_allowed("low", "medium") is true
   - Expected: manifest_cost_allowed("high", "medium") is false
   - Expected: medium contains `budget_low_llvm_pass`
   - Expected: medium does not contain `budget_high_llvm_pass`
   - Expected: high_budget contains `budget_high_llvm_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val low = manifest_pass_entry_new_with_backend_policy_and_cost(
    "budget_low_llvm_pass",
    [],
    PassScope.Function,
    [],
    ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure"),
    optimization_backend_policy_only([OptimizerBackendKind.Llvm], "llvm_only"),
    "low",
    "budget_low_llvm_pass_entry"
)
val high = manifest_pass_entry_new_with_backend_policy_and_cost(
    "budget_high_llvm_pass",
    [],
    PassScope.Function,
    [],
    ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure"),
    optimization_backend_policy_only([OptimizerBackendKind.Llvm], "llvm_only"),
    "high",
    "budget_high_llvm_pass_entry"
)
val manifest_result = load_manifest_v1_from_parsed(
    1,
    "simple.opt.mir.v1",
    "budget_llvm_plugin",
    "1.0.0",
    "0.9.0",
    [low, high]
)
expect(manifest_result.?).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result.?).to_equal(true)

val registry = registry_result.unwrap()
val medium = dynamic_pass_registry_names_for_backend_budget(registry, "llvm-lib", "medium")
val high_budget = dynamic_pass_registry_names_for_backend_budget(registry, "llvm", "high")

expect(manifest_cost_allowed("low", "medium")).to_equal(true)
expect(manifest_cost_allowed("high", "medium")).to_equal(false)
expect(medium.contains("budget_low_llvm_pass")).to_equal(true)
expect(medium.contains("budget_high_llvm_pass")).to_equal(false)
expect(high_budget.contains("budget_high_llvm_pass")).to_equal(true)
```

</details>

#### explains dynamic plugin backend and budget skip decisions

- ManifestPassContract
- optimization backend policy only
- ManifestPassContract
- optimization backend policy only
   - Expected: manifest_result.? is true
   - Expected: registry_result.? is true
   - Expected: backend_skip.pass_name equals `decision_low_llvm_pass`
   - Expected: backend_skip.applies is false
   - Expected: backend_skip.reason equals `llvm_only`
   - Expected: skipped.len() equals `1`
   - Expected: skipped[0].pass_name equals `decision_high_llvm_pass`
   - Expected: skipped[0].reason equals `cost budget exceeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val low = manifest_pass_entry_new_with_backend_policy_and_cost(
    "decision_low_llvm_pass",
    [],
    PassScope.Function,
    [],
    ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure"),
    optimization_backend_policy_only([OptimizerBackendKind.Llvm], "llvm_only"),
    "low",
    "decision_low_llvm_pass_entry"
)
val high = manifest_pass_entry_new_with_backend_policy_and_cost(
    "decision_high_llvm_pass",
    [],
    PassScope.Function,
    [],
    ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure"),
    optimization_backend_policy_only([OptimizerBackendKind.Llvm], "llvm_only"),
    "high",
    "decision_high_llvm_pass_entry"
)
val manifest_result = load_manifest_v1_from_parsed(
    1,
    "simple.opt.mir.v1",
    "decision_llvm_plugin",
    "1.0.0",
    "0.9.0",
    [low, high]
)
expect(manifest_result.?).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result.?).to_equal(true)

val registry = registry_result.unwrap()
val backend_skip = dynamic_pass_descriptor_backend_decision(registry.descriptors[0], "cranelift", "high")
expect(backend_skip.pass_name).to_equal("decision_low_llvm_pass")
expect(backend_skip.applies).to_equal(false)
expect(backend_skip.reason).to_equal("llvm_only")

val skipped = dynamic_pass_registry_skipped_decisions_for_backend_budget(registry, "llvm-lib", "medium")
expect(skipped.len()).to_equal(1)
expect(skipped[0].pass_name).to_equal("decision_high_llvm_pass")
expect(skipped[0].reason).to_equal("cost budget exceeded")
```

</details>

#### gates manifest rule anchors by backend and budget

- ManifestPassContract
- optimization backend policy only
   - Expected: manifest_result.? is true
   - Expected: registry_result.? is true
   - Expected: manifest_registered_pass_applies_to_backend_budget(registry, manifest, "llvm-lib", "high") is true
   - Expected: manifest_registered_pass_applies_to_backend_budget(registry, manifest, "llvm-lib", "medium") is false
   - Expected: manifest_registered_pass_applies_to_backend_budget(registry, manifest, "cranelift", "high") is false
   - Expected: rules_only_result.? is true
   - Expected: manifest_registered_pass_applies_to_backend_budget(registry, rules_only_result.unwrap(), "cranelift", "low") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val high = manifest_pass_entry_new_with_backend_policy_and_cost(
    "rule_anchor_high_llvm_pass",
    [],
    PassScope.Function,
    [],
    ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure"),
    optimization_backend_policy_only([OptimizerBackendKind.Llvm], "llvm_only"),
    "high",
    "rule_anchor_high_llvm_pass_entry"
)
val manifest_result = load_manifest_v1_from_parsed(
    1,
    "simple.opt.mir.v1",
    "rule_anchor_plugin",
    "1.0.0",
    "0.9.0",
    [high]
)
expect(manifest_result.?).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result.?).to_equal(true)

val registry = registry_result.unwrap()
val manifest = manifest_result.unwrap()
expect(manifest_registered_pass_applies_to_backend_budget(registry, manifest, "llvm-lib", "high")).to_equal(true)
expect(manifest_registered_pass_applies_to_backend_budget(registry, manifest, "llvm-lib", "medium")).to_equal(false)
expect(manifest_registered_pass_applies_to_backend_budget(registry, manifest, "cranelift", "high")).to_equal(false)

val rules_only_result = load_manifest_v1_from_parsed(
    1,
    "simple.opt.mir.v1",
    "rules_only_plugin",
    "1.0.0",
    "0.9.0",
    []
)
expect(rules_only_result.?).to_equal(true)
expect(manifest_registered_pass_applies_to_backend_budget(registry, rules_only_result.unwrap(), "cranelift", "low")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- optimizer manifest backend and cost budget policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
