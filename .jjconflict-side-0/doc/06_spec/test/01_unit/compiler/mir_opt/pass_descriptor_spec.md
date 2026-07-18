# Pass Descriptor Specification

> <details>

<!-- sdn-diagram:id=pass_descriptor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pass_descriptor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pass_descriptor_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pass_descriptor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pass Descriptor Specification

## Scenarios

### MIR optimization pass descriptors

#### exposes a reusable registry for optimization provider planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptors = mir_pass_descriptor_registry()
val providers = mir_pass_provider_registry()
expect(descriptors.len()).to_be_greater_than(10)
expect(providers.len()).to_equal(descriptors.len())
expect(providers[0].name).to_start_with("simple.opt.mir.")
```

</details>

#### preserves old short pass aliases through stable names

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dce = mir_pass_descriptor_for_name("dce")
expect(dce.?).to_equal(true)
expect(dce.unwrap().stable_name).to_equal("dead_code_elimination")

val const_fold = mir_pass_descriptor_for_name("const_fold")
expect(const_fold.?).to_equal(true)
expect(const_fold.unwrap().stable_name).to_equal("constant_folding")
```

</details>

#### routes vectorization alias to the stable auto-vectorize provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptor = mir_pass_descriptor_for_name("vectorization")
expect(descriptor.?).to_equal(true)
expect(descriptor.unwrap().stable_name).to_equal("auto_vectorize")
expect(mir_pass_provider_name("vectorization")).to_equal("simple.opt.mir.auto_vectorize")
```

</details>

#### routes legacy collection optimization alias to the collection provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptor = mir_pass_descriptor_for_name("collection_optimization")
expect(descriptor.?).to_equal(true)
expect(descriptor.unwrap().stable_name).to_equal("collection_opt")
expect(mir_pass_provider_name("collection_optimization")).to_equal("simple.opt.collection.loop_access")
expect(mir_pass_uses_pipeline_provider("collection_optimization")).to_equal(true)
```

</details>

#### exposes collection optimization as a hot pure Simple provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptor = mir_pass_descriptor_for_name("collection_opt")
expect(descriptor.?).to_equal(true)
val provider = descriptor.unwrap().provider
expect(provider.hot_path).to_equal(true)
expect(provider.required_facts).to_contain("loop_bounds")
expect(provider.required_facts).to_contain("collection_layout")
expect(provider.produced_facts).to_contain("canonical_collection_loops")
expect(provider.produced_facts).to_contain("loop_invariant_scalar_ops")
```

</details>

#### exposes strength reduction as a reusable optimization plugin provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptor = mir_pass_descriptor_for_name("strength_reduction")
expect(descriptor.?).to_equal(true)
expect(descriptor.unwrap().provider.name).to_equal("simple.opt.math.strength_reduce")
expect(mir_pass_uses_pipeline_provider("strength_reduction")).to_equal(true)
```

</details>

#### keeps low-level scalar cleanup in the Cranelift pipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val passes = optimizationpipeline_passes_for_backend(OptLevel.Aggressive, "cranlift")
expect(passes.contains("common_subexpr_elim")).to_equal(true)
expect(passes.contains("global_value_numbering")).to_equal(true)
expect(passes.contains("loop_unroll")).to_equal(true)
expect(passes.contains("strength_reduction")).to_equal(true)
```

</details>

#### skips LLVM-duplicated scalar cleanup in backend-aware pipelines

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mir_pass_applies_to_backend("strength_reduction", "llvm-lib")).to_equal(false)
expect(mir_pass_applies_to_backend("strength_reduction", "cranelift")).to_equal(true)
```

</details>

#### returns nil or empty metadata for unknown passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptor = mir_pass_descriptor_for_name("not_a_pass")
expect(descriptor.?).to_equal(false)
expect(mir_pass_provider_name("not_a_pass")).to_equal("")
expect(mir_pass_uses_pipeline_provider("not_a_pass")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/pass_descriptor_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
