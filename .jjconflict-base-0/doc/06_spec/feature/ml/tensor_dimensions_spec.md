# Tensor Dimension Inference Specification

| Field | Value |
|---|---|
| Source | `test/03_system/feature/ml/tensor_dimensions_spec.spl` |
| Feature IDs | `#193` |
| Category | ML |
| Status | Implemented |
| Requirements | `doc/02_requirements/feature/category/Data_Structures.md` |
| Design | `doc/05_design/tensor_dimensions_design.md` |
| Guide | `doc/07_guide/deep_learning/tensor_dimensions.md` |

## Overview

This SPipe spec replaces the legacy zero-test generated snapshot for tensor
dimensions with executable traceability checks over the current source model,
Lean regenerator, design doc, guide, and generated Lean proof artifact.

## Scenario Summary

| Metric | Count |
|---|---:|
| Total scenarios | 3 |
| Active scenarios | 3 |

## Scenarios

### Tensor dimension inference traceability

#### documents all dimension variants in the source model

```simple
val source = _read(MODEL_PATH)
expect(source).to_contain("enum Dim:")
expect(source).to_contain("Literal(value: i32)")
expect(source).to_contain("Var(variable: DimVar)")
expect(source).to_contain("Named(name: text, range: Option<(i32, i32)>)")
expect(source).to_contain("Dynamic")
expect(source).to_contain("Broadcast")
```

#### generates the Lean tensor dimensions verification model

```simple
val source = _read(REGEN_PATH)
expect(source).to_contain("fn regenerate_tensor_dimensions() -> text:")
expect(source).to_contain("TensorDimensions")
expect(source).to_contain("def unifyDim : Dim -> Dim -> UnifyResult")
expect(source).to_contain("def matmulShape (left right : TensorShape) : Option TensorShape :=")
```

#### keeps guide, design, and Lean proof artifacts linked

```simple
val guide = _read(GUIDE_PATH)
val design = _read(DESIGN_PATH)
val lean = _read(LEAN_PATH)
expect(guide).to_contain("Tensor Dimension")
expect(design).to_contain("Tensor dimension inference")
expect(lean).to_contain("namespace TensorDimensions")
```
