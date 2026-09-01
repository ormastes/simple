# Optimizer Manifest Backend Budget Specification

> Tests covering optimizer manifest backend and cost budget policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimizer Manifest Backend Budget Specification

## Scenarios

### optimizer manifest backend and cost budget policy

#### defaults manifest-created passes to all backends and medium cost

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults manifest-created passes to all backends and medium cost
   - Expected: manifest_result != nil is true
   - Expected: registry_result != nil is true
   - Expected: dynamic_pass_registry_names_for_backend(registry, "cranlift") contains `budget_default_pass`
   - Expected: dynamic_pass_registry_names_for_backend_budget(registry, "llvm-lib", "medium") contains `budget_default_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults manifest-created passes to all backends and medium cost")
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
expect(manifest_result != nil).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result != nil).to_equal(true)

val registry = registry_result.unwrap()
expect(dynamic_pass_registry_names_for_backend(registry, "cranlift").contains("budget_default_pass")).to_equal(true)
expect(dynamic_pass_registry_names_for_backend_budget(registry, "llvm-lib", "medium").contains("budget_default_pass")).to_equal(true)
```

</details>

#### loads backend policy and cost class from JSON manifests

- loads backend policy and cost class from JSON manifests
   - Expected: manifest_result != nil is true
   - Expected: manifest.name equals `json_budget_plugin`
   - Expected: manifest.passes.len() equals `1`
   - Expected: manifest.passes[0].cost_class equals `high`
   - Expected: registry_result != nil is true
   - Expected: dynamic_pass_registry_names_for_backend_budget(registry, "llvm-lib", "medium") does not contain `json_high_llvm_pass`
   - Expected: dynamic_pass_registry_names_for_backend_budget(registry, "llvm", "high") contains `json_high_llvm_pass`
   - Expected: dynamic_pass_registry_names_for_backend_budget(registry, "cranelift", "high") does not contain `json_high_llvm_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads backend policy and cost class from JSON manifests")
val json = "{\"schema_version\":1,\"compiler_abi\":\"simple.opt.mir.v1\",\"name\":\"json_budget_plugin\",\"version\":\"1.0.0\",\"min_compiler_version\":\"0.9.0\",\"passes\":[{\"stable_name\":\"json_high_llvm_pass\",\"aliases\":[\"json_llvm_alias\"],\"scope\":\"function\",\"capability_requires\":[\"typed_mir\"],\"contract\":{\"inputs\":[\"typed_mir\"],\"outputs\":[\"canonical_mir\"],\"purity\":\"pure\"},\"backend_policy\":{\"only\":[\"llvm\"],\"reason\":\"json_llvm_only\"},\"cost_class\":\"high\",\"entry_symbol\":\"json_high_llvm_pass_entry\"}]}"
val manifest_result = load_manifest_v1(json)
expect(manifest_result != nil).to_equal(true)
val manifest = manifest_result.unwrap()
expect(manifest.name).to_equal("json_budget_plugin")
expect(manifest.passes.len()).to_equal(1)
expect(manifest.passes[0].cost_class).to_equal("high")

val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest)
expect(registry_result != nil).to_equal(true)
val registry = registry_result.unwrap()
expect(dynamic_pass_registry_names_for_backend_budget(registry, "llvm-lib", "medium").contains("json_high_llvm_pass")).to_equal(false)
expect(dynamic_pass_registry_names_for_backend_budget(registry, "llvm", "high").contains("json_high_llvm_pass")).to_equal(true)
expect(dynamic_pass_registry_names_for_backend_budget(registry, "cranelift", "high").contains("json_high_llvm_pass")).to_equal(false)
```

</details>

#### skips high-cost LLVM-only dynamic plugins under a medium budget

- skips high-cost LLVM-only dynamic plugins under a medium budget
   - Expected: manifest_result != nil is true
   - Expected: registry_result != nil is true
   - Expected: manifest_cost_allowed("low", "medium") is true
   - Expected: manifest_cost_allowed("high", "medium") is false
   - Expected: medium contains `budget_low_llvm_pass`
   - Expected: medium does not contain `budget_high_llvm_pass`
   - Expected: high_budget contains `budget_high_llvm_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips high-cost LLVM-only dynamic plugins under a medium budget")
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
expect(manifest_result != nil).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result != nil).to_equal(true)

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

- explains dynamic plugin backend and budget skip decisions
   - Expected: manifest_result != nil is true
   - Expected: registry_result != nil is true
   - Expected: backend_skip.pass_name equals `decision_low_llvm_pass`
   - Expected: backend_skip.applies is false
   - Expected: backend_skip.reason equals `llvm_only`
   - Expected: skipped.len() equals `1`
   - Expected: skipped[0].pass_name equals `decision_high_llvm_pass`
   - Expected: skipped[0].reason equals `cost budget exceeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explains dynamic plugin backend and budget skip decisions")
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
expect(manifest_result != nil).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result != nil).to_equal(true)

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

- gates manifest rule anchors by backend and budget
   - Expected: manifest_result != nil is true
   - Expected: registry_result != nil is true
   - Expected: manifest_registered_pass_applies_to_backend_budget(registry, manifest, "llvm-lib", "high") is true
   - Expected: manifest_registered_pass_applies_to_backend_budget(registry, manifest, "llvm-lib", "medium") is false
   - Expected: manifest_registered_pass_applies_to_backend_budget(registry, manifest, "cranelift", "high") is false
   - Expected: rules_only_result != nil is true
   - Expected: manifest_registered_pass_applies_to_backend_budget(registry, rules_only_result.unwrap(), "cranelift", "low") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates manifest rule anchors by backend and budget")
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
expect(manifest_result != nil).to_equal(true)
val registry_result = dynamic_pass_registry_register(dynamic_pass_registry_new(), manifest_result.unwrap())
expect(registry_result != nil).to_equal(true)

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
expect(rules_only_result != nil).to_equal(true)
expect(manifest_registered_pass_applies_to_backend_budget(registry, rules_only_result.unwrap(), "cranelift", "low")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering optimizer manifest backend and cost budget policy.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5eaa49b14f042935079366ed6e026b3446f46967eb13d1fcf72261ee8d14d8d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5eaa49b14f042935079366ed6e026b3446f46967eb13d1fcf72261ee8d14d8d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5eaa49b14f042935079366ed6e026b3446f46967eb13d1fcf72261ee8d14d8d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.spl
mirror: doc/06_spec/unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults manifest-created passes to all backends and medium cost' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads backend policy and cost class from JSON manifests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips high-cost LLVM-only dynamic plugins under a medium budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
