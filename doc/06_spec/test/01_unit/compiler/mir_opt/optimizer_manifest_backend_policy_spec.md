# Optimizer Manifest Backend Policy Specification

> 1. ManifestPassContract

<!-- sdn-diagram:id=optimizer_manifest_backend_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=optimizer_manifest_backend_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

optimizer_manifest_backend_policy_spec -> std
optimizer_manifest_backend_policy_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=optimizer_manifest_backend_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimizer Manifest Backend Policy Specification

## Scenarios

### optimizer manifest backend policy for REQ-OPJH-023 REQ-OPJH-024

#### gives manifest-created passes an all-backend default

1. ManifestPassContract
   - Expected: optimization_rule_provider_applies_to_backend(desc.provider, OptimizerBackendKind.Cranelift) is true
   - Expected: optimization_rule_provider_applies_to_backend(desc.provider, OptimizerBackendKind.Llvm) is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = manifest_pass_entry_new(
    "ssa_var_canon",
    [],
    PassScope.Function,
    [],
    ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure"),
    "ssa_var_canon_entry"
)
val desc = dynamic_pass_descriptor_from_entry(entry, "jit_hotspot")

expect(optimization_rule_provider_applies_to_backend(desc.provider, OptimizerBackendKind.Cranelift)).to_equal(true)
expect(optimization_rule_provider_applies_to_backend(desc.provider, OptimizerBackendKind.Llvm)).to_equal(true)
```

</details>

#### preserves backend skip policies on dynamic descriptors

1. ManifestPassContract
   - Expected: optimization_rule_provider_applies_to_backend(provider, OptimizerBackendKind.Cranelift) is true
   - Expected: optimization_rule_provider_applies_to_backend(provider, OptimizerBackendKind.Llvm) is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = manifest_pass_entry_new(
    "simple_pre_sroa",
    [],
    PassScope.Function,
    [],
    ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure"),
    "simple_pre_sroa_entry"
)
val desc = dynamic_pass_descriptor_from_entry(entry, "jit_hotspot")
val policy = optimization_backend_policy_skip([OptimizerBackendKind.Llvm], "llvm_backend_runs_sroa")
val provider = optimization_rule_provider_with_backend_policy(desc.provider, policy)

expect(optimization_rule_provider_applies_to_backend(provider, OptimizerBackendKind.Cranelift)).to_equal(true)
expect(optimization_rule_provider_applies_to_backend(provider, OptimizerBackendKind.Llvm)).to_equal(false)
```

</details>

#### filters registered dynamic pass descriptors by backend policy

1. optimization backend policy only

2. optimization backend policy skip
   - Expected: manifest_result.? is true
   - Expected: registry_result.? is true
   - Expected: cranelift_names contains `backend_common_test_pass`
   - Expected: cranelift_names contains `backend_cranelift_test_pass`
   - Expected: cranelift_names contains `backend_skip_llvm_test_pass`
   - Expected: llvm_names contains `backend_common_test_pass`
   - Expected: llvm_names does not contain `backend_cranelift_test_pass`
   - Expected: llvm_names does not contain `backend_skip_llvm_test_pass`
   - Expected: llvm_skipped contains `backend_cranelift_test_pass`
   - Expected: llvm_skipped contains `backend_skip_llvm_test_pass`


<details>
<summary>Executable SPipe</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure")
val common = manifest_pass_entry_new(
    "backend_common_test_pass",
    [],
    PassScope.Function,
    [],
    contract,
    "backend_common_test_pass_entry"
)
val cranelift_only = manifest_pass_entry_new_with_backend_policy(
    "backend_cranelift_test_pass",
    [],
    PassScope.Function,
    [],
    contract,
    optimization_backend_policy_only([OptimizerBackendKind.Cranelift], "cranelift_only"),
    "backend_cranelift_test_pass_entry"
)
val skip_llvm = manifest_pass_entry_new_with_backend_policy(
    "backend_skip_llvm_test_pass",
    [],
    PassScope.Function,
    [],
    contract,
    optimization_backend_policy_skip([OptimizerBackendKind.Llvm], "llvm_runs_backend_pipeline"),
    "backend_skip_llvm_test_pass_entry"
)
val manifest_result = load_manifest_v1_from_parsed(
    1,
    "simple.opt.mir.v1",
    "backend_policy_test_plugin",
    "1.0.0",
    "0.9.0",
    [common, cranelift_only, skip_llvm]
)
expect(manifest_result.?).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result.?).to_equal(true)

val registry = registry_result.unwrap()
val cranelift_names = dynamic_pass_registry_names_for_backend(registry, "cranlift")
val llvm_names = dynamic_pass_registry_names_for_backend(registry, "llvm")
val llvm_skipped = dynamic_pass_registry_skipped_names_for_backend(registry, "llvm")

expect(cranelift_names.contains("backend_common_test_pass")).to_equal(true)
expect(cranelift_names.contains("backend_cranelift_test_pass")).to_equal(true)
expect(cranelift_names.contains("backend_skip_llvm_test_pass")).to_equal(true)
expect(llvm_names.contains("backend_common_test_pass")).to_equal(true)
expect(llvm_names.contains("backend_cranelift_test_pass")).to_equal(false)
expect(llvm_names.contains("backend_skip_llvm_test_pass")).to_equal(false)
expect(llvm_skipped.contains("backend_cranelift_test_pass")).to_equal(true)
expect(llvm_skipped.contains("backend_skip_llvm_test_pass")).to_equal(true)
```

</details>

#### filters registered dynamic pass descriptors by backend and compile-cost budget

1. optimization backend policy only

2. optimization backend policy only
   - Expected: manifest_result.? is true
   - Expected: registry_result.? is true
   - Expected: manifest_cost_allowed("low", "medium") is true
   - Expected: manifest_cost_allowed("high", "medium") is false
   - Expected: llvm_medium contains `backend_low_test_pass`
   - Expected: llvm_medium does not contain `backend_high_test_pass`
   - Expected: llvm_medium_skipped contains `backend_high_test_pass`


<details>
<summary>Executable SPipe</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure")
val low = manifest_pass_entry_new_with_backend_policy_and_cost(
    "backend_low_test_pass",
    [],
    PassScope.Function,
    [],
    contract,
    optimization_backend_policy_only([OptimizerBackendKind.Llvm], "llvm_only"),
    "low",
    "backend_low_test_pass_entry"
)
val high = manifest_pass_entry_new_with_backend_policy_and_cost(
    "backend_high_test_pass",
    [],
    PassScope.Function,
    [],
    contract,
    optimization_backend_policy_only([OptimizerBackendKind.Llvm], "llvm_only"),
    "high",
    "backend_high_test_pass_entry"
)
val manifest_result = load_manifest_v1_from_parsed(
    1,
    "simple.opt.mir.v1",
    "backend_budget_test_plugin",
    "1.0.0",
    "0.9.0",
    [low, high]
)
expect(manifest_result.?).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result.?).to_equal(true)

val registry = registry_result.unwrap()
val llvm_medium = dynamic_pass_registry_names_for_backend_budget(registry, "llvm-lib", "medium")
val llvm_medium_skipped = dynamic_pass_registry_skipped_names_for_backend_budget(registry, "llvm-lib", "medium")

expect(manifest_cost_allowed("low", "medium")).to_equal(true)
expect(manifest_cost_allowed("high", "medium")).to_equal(false)
expect(llvm_medium.contains("backend_low_test_pass")).to_equal(true)
expect(llvm_medium.contains("backend_high_test_pass")).to_equal(false)
expect(llvm_medium_skipped.contains("backend_high_test_pass")).to_equal(true)
```

</details>

#### runs manifest pattern rules only for backend-applicable dynamic passes

1. ManifestPassContract

2. optimization backend policy only

3. [remove copy rule
   - Expected: manifest_result.? is true
   - Expected: registry_result.? is true
   - Expected: cranelift_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `0`
   - Expected: llvm_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = manifest_pass_entry_new_with_backend_policy(
    "backend_rule_exec_test_pass",
    [],
    PassScope.Function,
    [],
    ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure"),
    optimization_backend_policy_only([OptimizerBackendKind.Cranelift], "cranelift_only"),
    "backend_rule_exec_test_pass_entry"
)
val manifest_result = load_manifest_v1_from_parsed_with_rules(
    1,
    "simple.opt.mir.v1",
    "backend_rule_exec_test_plugin",
    "1.0.0",
    "0.9.0",
    [entry],
    [remove_copy_rule()]
)
expect(manifest_result.?).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result.?).to_equal(true)

val registry = registry_result.unwrap()
val manifest = manifest_result.unwrap()
val cranelift_result = run_manifest_pattern_rules_for_backend(manifest_test_module(), registry, manifest, "cranlift")
val llvm_result = run_manifest_pattern_rules_for_backend(manifest_test_module(), registry, manifest, "llvm")

expect(cranelift_result.functions[SymbolId(id: 1)].blocks[0].instructions.len()).to_equal(0)
expect(llvm_result.functions[SymbolId(id: 1)].blocks[0].instructions.len()).to_equal(1)
```

</details>

#### does not run high-cost manifest pattern rules when JIT budget is medium

1. ManifestPassContract

2. optimization backend policy only

3. [remove copy rule
   - Expected: manifest_result.? is true
   - Expected: registry_result.? is true
   - Expected: llvm_medium_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `1`
   - Expected: llvm_high_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `0`
   - Expected: cranelift_high_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = manifest_pass_entry_new_with_backend_policy_and_cost(
    "backend_rule_budget_high_test_pass",
    [],
    PassScope.Function,
    [],
    ManifestPassContract(["typed_mir"], ["canonical_mir"], "pure"),
    optimization_backend_policy_only([OptimizerBackendKind.Llvm], "llvm_only"),
    "high",
    "backend_rule_budget_high_test_pass_entry"
)
val manifest_result = load_manifest_v1_from_parsed_with_rules(
    1,
    "simple.opt.mir.v1",
    "backend_rule_budget_test_plugin",
    "1.0.0",
    "0.9.0",
    [entry],
    [remove_copy_rule()]
)
expect(manifest_result.?).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result.?).to_equal(true)

val registry = registry_result.unwrap()
val manifest = manifest_result.unwrap()
val llvm_medium_result = run_manifest_pattern_rules_for_backend_budget(manifest_test_module(), registry, manifest, "llvm", "medium")
val llvm_high_result = run_manifest_pattern_rules_for_backend_budget(manifest_test_module(), registry, manifest, "llvm", "high")
val cranelift_high_result = run_manifest_pattern_rules_for_backend_budget(manifest_test_module(), registry, manifest, "cranelift", "high")

expect(llvm_medium_result.functions[SymbolId(id: 1)].blocks[0].instructions.len()).to_equal(1)
expect(llvm_high_result.functions[SymbolId(id: 1)].blocks[0].instructions.len()).to_equal(0)
expect(cranelift_high_result.functions[SymbolId(id: 1)].blocks[0].instructions.len()).to_equal(1)
```

</details>

#### loads JSON pattern rules and gates execution by backend budget

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"schema_version\":1,\"compiler_abi\":\"simple.opt.mir.v1\",\"name\":\"json_rule_budget_plugin\",\"version\":\"1.0.0\",\"min_compiler_version\":\"0.9.0\",\"passes\":[{\"stable_name\":\"json_rule_high_llvm_pass\",\"aliases\":[],\"scope\":\"function\",\"capability_requires\":[],\"contract\":{\"inputs\":[\"typed_mir\"],\"outputs\":[\"canonical_mir\"],\"purity\":\"pure\"},\"backend_policy\":{\"only\":[\"llvm\"],\"reason\":\"json_llvm_only\"},\"cost_class\":\"high\",\"entry_symbol\":\"json_rule_high_llvm_pass_entry\"}],\"rules\":[{\"name\":\"json_remove_copy\",\"pattern\":{\"inst_count\":1,\"slots\":[{\"kind_tag\":\"Copy\",\"operand_0\":\"$src\",\"operand_1\":null,\"dest\":\"$dest\"}]},\"rewrite\":{\"kind_tag\":\"Remove\",\"dest\":\"$dest\",\"operands\":[]},\"cost_delta\":-1,\"safety\":\"test\"}]}"
val manifest_result = load_manifest_v1(json)
expect(manifest_result.?).to_equal(true)
val manifest = manifest_result.unwrap()
expect(manifest.rules.len()).to_equal(1)

val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest)
expect(registry_result.?).to_equal(true)
val registry = registry_result.unwrap()

val llvm_medium_result = run_manifest_pattern_rules_for_backend_budget(manifest_test_module(), registry, manifest, "llvm", "medium")
val llvm_high_result = run_manifest_pattern_rules_for_backend_budget(manifest_test_module(), registry, manifest, "llvm", "high")
val cranelift_high_result = run_manifest_pattern_rules_for_backend_budget(manifest_test_module(), registry, manifest, "cranelift", "high")

expect(llvm_medium_result.functions[SymbolId(id: 1)].blocks[0].instructions.len()).to_equal(1)
expect(llvm_high_result.functions[SymbolId(id: 1)].blocks[0].instructions.len()).to_equal(0)
expect(cranelift_high_result.functions[SymbolId(id: 1)].blocks[0].instructions.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- optimizer manifest backend policy for REQ-OPJH-023 REQ-OPJH-024

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
