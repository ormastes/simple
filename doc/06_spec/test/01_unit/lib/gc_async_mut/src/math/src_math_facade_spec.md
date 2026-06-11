# Src Math Facade Specification

> <details>

<!-- sdn-diagram:id=src_math_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=src_math_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

src_math_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=src_math_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Src Math Facade Specification

## Scenarios

### gc_async_mut src math facade

#### re-exports backend selection and rendering format metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MathBackend.CPU.is_available()).to_equal(true)
expect(MathBackend.CPU.to_string()).to_equal("cpu")
expect(RenderFormat.LaTeX.to_string()).to_equal("latex")
val cap = BackendCapability.for_backend(MathBackend.CPU)
expect(cap.supports_tensor).to_equal(true)
expect(cap.supports_symbolic).to_equal(true)
expect(select_backend(MathBackend.CPU)).to_equal(MathBackend.CPU)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/src/math/src_math_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut src math facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
