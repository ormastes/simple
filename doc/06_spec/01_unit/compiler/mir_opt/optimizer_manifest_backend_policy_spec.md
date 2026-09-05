# Optimizer Manifest Backend Policy Specification

> Tests covering optimizer manifest backend policy for REQ-OPJH-023 REQ-OPJH-024.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimizer Manifest Backend Policy Specification

## Scenarios

### optimizer manifest backend policy for REQ-OPJH-023 REQ-OPJH-024

#### gives manifest-created passes an all-backend default

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-OPJH-023
# @req REQ-OPJH-024
```

</details>

#### preserves backend skip policies on dynamic descriptors

- preserves backend skip policies on dynamic descriptors
   - Expected: optimization_rule_provider_applies_to_backend(provider, OptimizerBackendKind.Cranelift) is true
   - Expected: optimization_rule_provider_applies_to_backend(provider, OptimizerBackendKind.Llvm) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves backend skip policies on dynamic descriptors")
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

- filters registered dynamic pass descriptors by backend policy
   - Expected: manifest_result != nil is true
   - Expected: registry_result != nil is true
   - Expected: cranelift_names contains `backend_common_test_pass`
   - Expected: cranelift_names contains `backend_cranelift_test_pass`
   - Expected: cranelift_names contains `backend_skip_llvm_test_pass`
   - Expected: llvm_names contains `backend_common_test_pass`
   - Expected: llvm_names does not contain `backend_cranelift_test_pass`
   - Expected: llvm_names does not contain `backend_skip_llvm_test_pass`
   - Expected: llvm_skipped contains `backend_cranelift_test_pass`
   - Expected: llvm_skipped contains `backend_skip_llvm_test_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("filters registered dynamic pass descriptors by backend policy")
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
expect(manifest_result != nil).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result != nil).to_equal(true)

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

- filters registered dynamic pass descriptors by backend and compile-cost budget
   - Expected: manifest_result != nil is true
   - Expected: registry_result != nil is true
   - Expected: manifest_cost_allowed("low", "medium") is true
   - Expected: manifest_cost_allowed("high", "medium") is false
   - Expected: llvm_medium contains `backend_low_test_pass`
   - Expected: llvm_medium does not contain `backend_high_test_pass`
   - Expected: llvm_medium_skipped contains `backend_high_test_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("filters registered dynamic pass descriptors by backend and compile-cost budget")
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
expect(manifest_result != nil).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result != nil).to_equal(true)

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

- runs manifest pattern rules only for backend-applicable dynamic passes
   - Expected: manifest_result != nil is true
   - Expected: registry_result != nil is true
   - Expected: cranelift_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `0`
   - Expected: llvm_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("runs manifest pattern rules only for backend-applicable dynamic passes")
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
expect(manifest_result != nil).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result != nil).to_equal(true)

val registry = registry_result.unwrap()
val manifest = manifest_result.unwrap()
val cranelift_result = run_manifest_pattern_rules_for_backend(manifest_test_module(), registry, manifest, "cranlift")
val llvm_result = run_manifest_pattern_rules_for_backend(manifest_test_module(), registry, manifest, "llvm")

expect(cranelift_result.functions[SymbolId(id: 1)].blocks[0].instructions.len()).to_equal(0)
expect(llvm_result.functions[SymbolId(id: 1)].blocks[0].instructions.len()).to_equal(1)
```

</details>

#### does not run high-cost manifest pattern rules when JIT budget is medium

- does not run high-cost manifest pattern rules when JIT budget is medium
   - Expected: manifest_result != nil is true
   - Expected: registry_result != nil is true
   - Expected: llvm_medium_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `1`
   - Expected: llvm_high_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `0`
   - Expected: cranelift_high_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not run high-cost manifest pattern rules when JIT budget is medium")
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
expect(manifest_result != nil).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result != nil).to_equal(true)

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

- loads JSON pattern rules and gates execution by backend budget
   - Expected: manifest_result != nil is true
   - Expected: manifest.rules.len() equals `1`
   - Expected: registry_result != nil is true
   - Expected: llvm_medium_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `1`
   - Expected: llvm_high_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `0`
   - Expected: cranelift_high_result.functions[SymbolId(id: 1)].blocks[0].instructions.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads JSON pattern rules and gates execution by backend budget")
val json = "{\"schema_version\":1,\"compiler_abi\":\"simple.opt.mir.v1\",\"name\":\"json_rule_budget_plugin\",\"version\":\"1.0.0\",\"min_compiler_version\":\"0.9.0\",\"passes\":[{\"stable_name\":\"json_rule_high_llvm_pass\",\"aliases\":[],\"scope\":\"function\",\"capability_requires\":[],\"contract\":{\"inputs\":[\"typed_mir\"],\"outputs\":[\"canonical_mir\"],\"purity\":\"pure\"},\"backend_policy\":{\"only\":[\"llvm\"],\"reason\":\"json_llvm_only\"},\"cost_class\":\"high\",\"entry_symbol\":\"json_rule_high_llvm_pass_entry\"}],\"rules\":[{\"name\":\"json_remove_copy\",\"pattern\":{\"inst_count\":1,\"slots\":[{\"kind_tag\":\"Copy\",\"operand_0\":\"$src\",\"operand_1\":null,\"dest\":\"$dest\"}]},\"rewrite\":{\"kind_tag\":\"Remove\",\"dest\":\"$dest\",\"operands\":[]},\"cost_delta\":-1,\"safety\":\"test\"}]}"
val manifest_result = load_manifest_v1(json)
expect(manifest_result != nil).to_equal(true)
val manifest = manifest_result.unwrap()
expect(manifest.rules.len()).to_equal(1)

val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest)
expect(registry_result != nil).to_equal(true)
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering optimizer manifest backend policy for REQ-OPJH-023 REQ-OPJH-024.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-OPJH-023`
- `REQ-OPJH-024":`
- `REQ-OPJH-024`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bbe1b50127289dd8c187e62105c1890e7fae9af5d0fe2725ee8175b685a52402`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bbe1b50127289dd8c187e62105c1890e7fae9af5d0fe2725ee8175b685a52402`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bbe1b50127289dd8c187e62105c1890e7fae9af5d0fe2725ee8175b685a52402`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.spl:121:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'gives manifest-created passes an all-backend default' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves backend skip policies on dynamic descriptors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters registered dynamic pass descriptors by backend policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.spl:215:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters registered dynamic pass descriptors by backend and compile-cost budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
