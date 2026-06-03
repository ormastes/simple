# Attributes Specification

## Scenarios

### FunctionAttr

### parse_function_attrs

#### parses bare fast_math

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fa = parse_function_attrs([make_attr("fast_math")])
expect(fa.has_fast_math).to_equal(true)
```

</details>

#### parses bare simd as enabled

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fa = parse_function_attrs([make_attr("simd")])
expect(fa.is_simd).to_equal(true)
expect(fa.simd_enable).to_equal(true)
```

</details>

#### parses simd(disable)

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fa = parse_function_attrs([make_simd_attr("disable")])
expect(fa.is_simd).to_equal(true)
expect(fa.simd_disable).to_equal(true)
```

</details>

#### parses simd(prefer_scalable)

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fa = parse_function_attrs([make_simd_attr("prefer_scalable")])
expect(fa.is_simd).to_equal(true)
expect(fa.simd_prefer_scalable).to_equal(true)
```

</details>

#### default function attrs leave fast_math false

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fa = FunctionAttr.default()
expect(fa.has_fast_math).to_equal(false)
```

</details>

#### parses GPU target metadata from gpu attribute

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fa = parse_function_attrs([make_gpu_target_attr("opencl")])
expect(fa.is_gpu_kernel).to_equal(true)
expect(fa.gpu_target).to_equal("opencl")
```

</details>

#### parses GPU backend ordering metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fa = parse_function_attrs([make_gpu_backends_attr("cuda,opencl")])
expect(fa.is_gpu_kernel).to_equal(true)
expect(fa.gpu_backends).to_equal("cuda,opencl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/common/attributes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FunctionAttr
- parse_function_attrs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
