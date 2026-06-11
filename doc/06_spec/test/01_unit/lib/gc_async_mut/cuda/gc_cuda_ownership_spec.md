# Gc Cuda Ownership Specification

> <details>

<!-- sdn-diagram:id=gc_cuda_ownership_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_cuda_ownership_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_cuda_ownership_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_cuda_ownership_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Cuda Ownership Specification

## Scenarios

### GC CUDA Ownership

### CudaStreamWrapper

#### owned stream frees on drop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = owned_stream(42)
expect(s.should_free()).to_equal(true)
```

</details>

#### borrowed stream does not free

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = borrowed_stream(42)
expect(s.should_free()).to_equal(false)
```

</details>

### CudaEventWrapper

#### owned event frees on drop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = owned_event(99)
expect(e.should_free()).to_equal(true)
```

</details>

### CudaDeviceMemWrapper

#### owned memory frees on drop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = owned_mem(100)
expect(m.should_free()).to_equal(true)
```

</details>

### Ownership transfer

#### only owner frees shared handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val owner = owned_stream(77)
val borrower = borrowed_stream(77)
# Borrower should not free
expect(borrower.should_free()).to_equal(false)
# Owner should free
expect(owner.should_free()).to_equal(true)
# Same handle
expect(owner.handle).to_equal(borrower.handle)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/cuda/gc_cuda_ownership_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GC CUDA Ownership
- CudaStreamWrapper
- CudaEventWrapper
- CudaDeviceMemWrapper
- Ownership transfer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
