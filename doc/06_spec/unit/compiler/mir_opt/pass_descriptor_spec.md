# Pass Descriptor Specification

> Tests covering MIR optimization pass descriptors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pass Descriptor Specification

## Scenarios

### MIR optimization pass descriptors

#### exposes a reusable registry for optimization provider planning

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes a reusable registry for optimization provider planning
   - Expected: providers.len() equals `descriptors.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes a reusable registry for optimization provider planning")
val descriptors = mir_pass_descriptor_registry()
val providers = mir_pass_provider_registry()
expect(descriptors.len()).to_be_greater_than(10)
expect(providers.len()).to_equal(descriptors.len())
expect(providers[0].name).to_start_with("simple.opt.mir.")
```

</details>

#### preserves old short pass aliases through stable names

- preserves old short pass aliases through stable names
   - Expected: dce != nil is true
   - Expected: dce.unwrap().stable_name equals `dead_code_elimination`
   - Expected: const_fold != nil is true
   - Expected: const_fold.unwrap().stable_name equals `constant_folding`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves old short pass aliases through stable names")
val dce = mir_pass_descriptor_for_name("dce")
expect(dce != nil).to_equal(true)
expect(dce.unwrap().stable_name).to_equal("dead_code_elimination")

val const_fold = mir_pass_descriptor_for_name("const_fold")
expect(const_fold != nil).to_equal(true)
expect(const_fold.unwrap().stable_name).to_equal("constant_folding")
```

</details>

#### routes vectorization alias to the stable auto-vectorize provider

- routes vectorization alias to the stable auto-vectorize provider
   - Expected: descriptor != nil is true
   - Expected: descriptor.unwrap().stable_name equals `auto_vectorize`
   - Expected: mir_pass_provider_name("vectorization") equals `simple.opt.mir.auto_vectorize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes vectorization alias to the stable auto-vectorize provider")
val descriptor = mir_pass_descriptor_for_name("vectorization")
expect(descriptor != nil).to_equal(true)
expect(descriptor.unwrap().stable_name).to_equal("auto_vectorize")
expect(mir_pass_provider_name("vectorization")).to_equal("simple.opt.mir.auto_vectorize")
```

</details>

#### routes legacy collection optimization alias to the collection provider

- routes legacy collection optimization alias to the collection provider
   - Expected: descriptor != nil is true
   - Expected: descriptor.unwrap().stable_name equals `collection_opt`
   - Expected: mir_pass_provider_name("collection_optimization") equals `simple.opt.collection.loop_access`
   - Expected: mir_pass_uses_pipeline_provider("collection_optimization") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes legacy collection optimization alias to the collection provider")
val descriptor = mir_pass_descriptor_for_name("collection_optimization")
expect(descriptor != nil).to_equal(true)
expect(descriptor.unwrap().stable_name).to_equal("collection_opt")
expect(mir_pass_provider_name("collection_optimization")).to_equal("simple.opt.collection.loop_access")
expect(mir_pass_uses_pipeline_provider("collection_optimization")).to_equal(true)
```

</details>

#### exposes collection optimization as a hot pure Simple provider

- exposes collection optimization as a hot pure Simple provider
   - Expected: descriptor != nil is true
   - Expected: provider.hot_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes collection optimization as a hot pure Simple provider")
val descriptor = mir_pass_descriptor_for_name("collection_opt")
expect(descriptor != nil).to_equal(true)
val provider = descriptor.unwrap().provider
expect(provider.hot_path).to_equal(true)
expect(provider.required_facts).to_contain("loop_bounds")
expect(provider.required_facts).to_contain("collection_layout")
expect(provider.produced_facts).to_contain("canonical_collection_loops")
expect(provider.produced_facts).to_contain("loop_invariant_scalar_ops")
```

</details>

#### exposes strength reduction as a reusable optimization plugin provider

- exposes strength reduction as a reusable optimization plugin provider
   - Expected: descriptor != nil is true
   - Expected: descriptor.unwrap().provider.name equals `simple.opt.math.strength_reduce`
   - Expected: mir_pass_uses_pipeline_provider("strength_reduction") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes strength reduction as a reusable optimization plugin provider")
val descriptor = mir_pass_descriptor_for_name("strength_reduction")
expect(descriptor != nil).to_equal(true)
expect(descriptor.unwrap().provider.name).to_equal("simple.opt.math.strength_reduce")
expect(mir_pass_uses_pipeline_provider("strength_reduction")).to_equal(true)
```

</details>

#### keeps low-level scalar cleanup in the Cranelift pipeline

- keeps low-level scalar cleanup in the Cranelift pipeline
   - Expected: passes contains `common_subexpr_elim`
   - Expected: passes contains `global_value_numbering`
   - Expected: passes contains `loop_unroll`
   - Expected: passes contains `strength_reduction`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps low-level scalar cleanup in the Cranelift pipeline")
val passes = optimizationpipeline_passes_for_backend(OptLevel.Aggressive, "cranlift")
expect(passes.contains("common_subexpr_elim")).to_equal(true)
expect(passes.contains("global_value_numbering")).to_equal(true)
expect(passes.contains("loop_unroll")).to_equal(true)
expect(passes.contains("strength_reduction")).to_equal(true)
```

</details>

#### skips LLVM-duplicated scalar cleanup in backend-aware pipelines

- skips LLVM-duplicated scalar cleanup in backend-aware pipelines
   - Expected: passes contains `dead_code_elimination`
   - Expected: passes contains `bounds_check_elimination`
   - Expected: passes does not contain `common_subexpr_elim`
   - Expected: passes does not contain `global_value_numbering`
   - Expected: passes does not contain `loop_unroll`
   - Expected: passes does not contain `strength_reduction`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips LLVM-duplicated scalar cleanup in backend-aware pipelines")
val passes = optimizationpipeline_passes_for_backend(OptLevel.Aggressive, "llvm")
expect(passes.contains("dead_code_elimination")).to_equal(true)
expect(passes.contains("bounds_check_elimination")).to_equal(true)
expect(passes.contains("common_subexpr_elim")).to_equal(false)
expect(passes.contains("global_value_numbering")).to_equal(false)
expect(passes.contains("loop_unroll")).to_equal(false)
expect(passes.contains("strength_reduction")).to_equal(false)
```

</details>

#### treats llvm-lib as LLVM for pass backend policy

- treats llvm-lib as LLVM for pass backend policy
   - Expected: mir_pass_applies_to_backend("strength_reduction", "llvm-lib") is false
   - Expected: mir_pass_applies_to_backend("strength_reduction", "cranelift") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats llvm-lib as LLVM for pass backend policy")
expect(mir_pass_applies_to_backend("strength_reduction", "llvm-lib")).to_equal(false)
expect(mir_pass_applies_to_backend("strength_reduction", "cranelift")).to_equal(true)
```

</details>

#### returns nil or empty metadata for unknown passes

- returns nil or empty metadata for unknown passes
   - Expected: descriptor != nil is false
   - Expected: mir_pass_provider_name("not_a_pass") equals ``
   - Expected: mir_pass_uses_pipeline_provider("not_a_pass") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil or empty metadata for unknown passes")
val descriptor = mir_pass_descriptor_for_name("not_a_pass")
expect(descriptor != nil).to_equal(false)
expect(mir_pass_provider_name("not_a_pass")).to_equal("")
expect(mir_pass_uses_pipeline_provider("not_a_pass")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/mir_opt/pass_descriptor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR optimization pass descriptors.
- MIR optimization pass descriptors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `a2b2a99549da2b85f4e9c19e138fe5cd11f79c3cc43451a00cd98d808abbff2d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2b2a99549da2b85f4e9c19e138fe5cd11f79c3cc43451a00cd98d808abbff2d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2b2a99549da2b85f4e9c19e138fe5cd11f79c3cc43451a00cd98d808abbff2d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/mir_opt/pass_descriptor_spec.spl
mirror: doc/06_spec/unit/compiler/mir_opt/pass_descriptor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mir_opt/pass_descriptor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mir_opt/pass_descriptor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mir_opt/pass_descriptor_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes a reusable registry for optimization provider planning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/pass_descriptor_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves old short pass aliases through stable names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/pass_descriptor_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes vectorization alias to the stable auto-vectorize provider' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
