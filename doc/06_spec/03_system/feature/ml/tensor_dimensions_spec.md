# Tensor Dimension Inference Specification

> Verifies the current tensor dimension inference artifact set: the source model defines concrete, named, variable, dynamic, and broadcast dimensions; the Lean regenerator emits the matching verification model; and public docs point at the same feature.

<!-- sdn-diagram:id=tensor_dimensions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_dimensions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_dimensions_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_dimensions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Dimension Inference Specification

Verifies the current tensor dimension inference artifact set: the source model defines concrete, named, variable, dynamic, and broadcast dimensions; the Lean regenerator emits the matching verification model; and public docs point at the same feature.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #193 |
| Category | ML |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/category/Data_Structures.md |
| Plan | N/A |
| Design | doc/05_design/tensor_dimensions_design.md |
| Research | N/A |
| Source | `test/03_system/feature/ml/tensor_dimensions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the current tensor dimension inference artifact set: the source model
defines concrete, named, variable, dynamic, and broadcast dimensions; the Lean
regenerator emits the matching verification model; and public docs point at the
same feature.

## Scenarios

### Tensor dimension inference traceability

#### documents all dimension variants in the source model

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read(MODEL_PATH)
expect(source).to_contain("enum Dim:")
expect(source).to_contain("Literal(value: i32)")
expect(source).to_contain("Var(variable: DimVar)")
expect(source).to_contain("Named(name: text, range: Option<(i32, i32)>)")
expect(source).to_contain("Dynamic")
expect(source).to_contain("Broadcast")
```

</details>

#### generates the Lean tensor dimensions verification model

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read(REGEN_PATH)
expect(source).to_contain("fn regenerate_tensor_dimensions() -> text:")
expect(source).to_contain("TensorDimensions")
expect(source).to_contain("def unifyDim : Dim → Dim → UnifyResult")
expect(source).to_contain("def matmulShape (left right : TensorShape) : Option TensorShape :=")
```

</details>

#### keeps guide, design, and Lean proof artifacts linked

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guide = _read(GUIDE_PATH)
val design = _read(DESIGN_PATH)
val lean = _read(LEAN_PATH)
expect(guide).to_contain("Tensor Dimension")
expect(design).to_contain("Tensor dimension inference")
expect(lean).to_contain("namespace TensorDimensions")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/category/Data_Structures.md](doc/02_requirements/feature/category/Data_Structures.md)
- **Design:** [doc/05_design/tensor_dimensions_design.md](doc/05_design/tensor_dimensions_design.md)


</details>
