# Gpu Target Metadata Specification

> <details>

<!-- sdn-diagram:id=gpu_target_metadata_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_target_metadata_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_target_metadata_spec -> std
gpu_target_metadata_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_target_metadata_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Target Metadata Specification

## Scenarios

### MIR GPU target metadata

#### lowers frontend-shaped gpu attribute metadata into MIR

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed_attr = parse_function_attrs([make_gpu_source_attr("opencl")])
val lowerer = MirLowering.new(SymbolTable.new())
val fn_ = make_mir_function("gpu_kernel")

val result = lowerer.apply_function_attr_to_mir(fn_, parsed_attr)

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("opencl")
expect(result.gpu_backend_order).to_equal("opencl")
```

</details>

#### propagates normalized OpenCL target metadata from function attrs

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lowerer = MirLowering.new(SymbolTable.new())
val fn_ = make_mir_function("gpu_kernel")
val attr = make_gpu_attr("opencl-spirv", "")

val result = lowerer.apply_function_attr_to_mir(fn_, attr)

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("opencl")
expect(result.gpu_backend_order).to_equal("opencl")
```

</details>

#### propagates normalized ROCm target metadata as HIP from function attrs

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lowerer = MirLowering.new(SymbolTable.new())
val fn_ = make_mir_function("gpu_kernel")
val attr = make_gpu_attr("rocm", "")

val result = lowerer.apply_function_attr_to_mir(fn_, attr)

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("hip")
expect(result.gpu_backend_order).to_equal("hip")
```

</details>

#### preserves canonical explicit backend order through MirFunction copies

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ = make_mir_function("gpu_kernel")
val attr = parse_function_attrs([make_gpu_source_attr_with_backends("auto", "rocm,cl,cuda")])
val lowerer = MirLowering.new(SymbolTable.new())
val tagged = lowerer.apply_function_attr_to_mir(fn_, attr)

val copied = MirFunction.with_blocks(tagged, [empty_block("replacement")])

expect(copied.is_kernel).to_equal(true)
expect(copied.gpu_target).to_equal("auto")
expect(copied.gpu_backend_order).to_equal("hip,opencl,cuda")
```

</details>

#### canonicalizes explicit backend order metadata through common aliases

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_gpu_backend_order_metadata("rocm, cl, nvptx")).to_equal("hip,opencl,cuda")

val fn_ = make_mir_function("gpu_kernel")
val attr = make_gpu_attr("auto", " hip-cpp, opencl-spirv, ptx ")
val lowerer = MirLowering.new(SymbolTable.new())

val result = lowerer.apply_function_attr_to_mir(fn_, attr)

expect(result.gpu_target).to_equal("auto")
expect(result.gpu_backend_order).to_equal("hip,opencl,cuda")
```

</details>

#### preserves positional GPU target metadata through HIR and MIR lowering

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = parse_function_attrs([make_gpu_source_attr("opencl")])

val result = lower_hir_attr_function_to_mir(attr, "positional_opencl_kernel")

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("opencl")
expect(result.gpu_backend_order).to_equal("opencl")
```

</details>

#### preserves named GPU target metadata through HIR and MIR lowering

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = parse_function_attrs([make_gpu_source_attr_with_backends("opencl", "")])

val result = lower_hir_attr_function_to_mir(attr, "named_opencl_kernel")

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("opencl")
expect(result.gpu_backend_order).to_equal("opencl")
```

</details>

#### preserves named GPU backend order metadata through HIR and MIR lowering

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attr = parse_function_attrs([make_gpu_source_attr_with_backends("auto", "rocm,cl,cuda")])

val result = lower_hir_attr_function_to_mir(attr, "ordered_gpu_kernel")

expect(result.is_kernel).to_equal(true)
expect(result.gpu_target).to_equal("auto")
expect(result.gpu_backend_order).to_equal("hip,opencl,cuda")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/gpu_target_metadata_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MIR GPU target metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
