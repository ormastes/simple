# Gpu Memory Roundtrip Specification

> <details>

<!-- sdn-diagram:id=gpu_memory_roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_memory_roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_memory_roundtrip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_memory_roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Memory Roundtrip Specification

## Scenarios

### GpuArray CPU fallback round-trip

#### upload then download round-trips data on None_ backend

- data push
- data push
- data push
- var arr = gpu alloc upload
   - Expected: out.len() equals `3`
   - Expected: first_ok is true
   - Expected: last_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_none()
var data: [f32] = []
data.push(1.5)
data.push(2.5)
data.push(-3.0)
var arr = gpu_alloc_upload(g, data)
val out = arr.download()
expect(out.len()).to_equal(3)
val first_ok = out[0] == 1.5
expect(first_ok).to_equal(true)
val last_ok = out[2] == -3.0
expect(last_ok).to_equal(true)
```

</details>

#### gpu_alloc yields count zeros on None_ backend

- data push
- data push
- data push
- data push
- var arr = gpu alloc upload
- var fresh = gpu alloc zeros
   - Expected: out.len() equals `4`
   - Expected: zero_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_none()
var data: [f32] = []
data.push(0.0)
data.push(0.0)
data.push(0.0)
data.push(0.0)
var arr = gpu_alloc_upload(g, data)
var fresh = gpu_alloc_zeros(g, 4)
val out = fresh.download()
expect(out.len()).to_equal(4)
val zero_ok = out[0] == 0.0 and out[3] == 0.0
expect(zero_ok).to_equal(true)
```

</details>

#### upload rejects size mismatch

- data push
- data push
- var arr = gpu alloc upload
- wrong push
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_none()
var data: [f32] = []
data.push(1.0)
data.push(2.0)
var arr = gpu_alloc_upload(g, data)
var wrong: [f32] = []
wrong.push(9.0)
val ok = arr.upload(wrong)
expect(ok).to_equal(false)
```

</details>

#### copy preserves host data on None_ backend

- data push
- var arr = gpu alloc upload
- var dup = gpu copy
   - Expected: out.len() equals `1`
   - Expected: val_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_none()
var data: [f32] = []
data.push(7.0)
var arr = gpu_alloc_upload(g, data)
var dup = gpu_copy(arr)
val out = dup.download()
expect(out.len()).to_equal(1)
val val_ok = out[0] == 7.0
expect(val_ok).to_equal(true)
```

</details>

#### copy_to transfers host data between None_ arrays

- src data push
- src data push
- var src = gpu alloc upload
- var dst = gpu alloc zeros
   - Expected: ok is true
   - Expected: out.len() equals `2`
   - Expected: moved_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_none()
var src_data: [f32] = []
src_data.push(4.0)
src_data.push(5.0)
var src = gpu_alloc_upload(g, src_data)
var dst = gpu_alloc_zeros(g, 2)
val ok = src.copy_to(dst)
expect(ok).to_equal(true)
val out = dst.download()
expect(out.len()).to_equal(2)
val moved_ok = out[1] == 5.0
expect(moved_ok).to_equal(true)
```

</details>

#### free clears host data and is idempotent

- data push
- var arr = gpu alloc upload
- arr free
- arr free
   - Expected: out.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_none()
var data: [f32] = []
data.push(1.0)
var arr = gpu_alloc_upload(g, data)
arr.free()
arr.free()
val out = arr.download()
expect(out.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/gpu_memory_roundtrip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GpuArray CPU fallback round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
