# Render 2d X86 Session Specification

> <details>

<!-- sdn-diagram:id=render_2d_x86_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=render_2d_x86_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

render_2d_x86_session_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=render_2d_x86_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render 2d X86 Session Specification

## Scenarios

### Render2dX86Session

#### x86_64 CUDA handle is_ok reports true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_cuda_handle_x86_64()
expect(h.is_ok()).to_equal(true)
expect(h.target_arch).to_equal("x86_64")
expect(h.target_bits).to_equal(64)
expect(h.error == Render2dX86InitError.None).to_equal(true)
```

</details>

#### x86_64 CUDA handle carries Cuda backend kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_cuda_handle_x86_64()
expect(h.base.kind == BackendSessionKind.Cuda).to_equal(true)
expect(h.base.device_name).to_equal("cuda:0")
```

</details>

#### x86_64 Vulkan handle is_ok reports true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_vulkan_handle_x86_64()
expect(h.is_ok()).to_equal(true)
expect(h.target_bits).to_equal(64)
expect(h.error == Render2dX86InitError.None).to_equal(true)
```

</details>

#### x86_64 Vulkan handle carries Vulkan backend kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_vulkan_handle_x86_64()
expect(h.base.kind == BackendSessionKind.Vulkan).to_equal(true)
expect(h.base.device_name).to_equal("vulkan:0")
```

</details>

#### x86_32 returns Arch32GpuUnavailable diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_x86_32_diagnostic()
expect(h.is_ok()).to_equal(false)
expect(h.is_null()).to_equal(true)
expect(h.error == Render2dX86InitError.Arch32GpuUnavailable).to_equal(true)
expect(h.target_bits).to_equal(32)
expect(h.target_arch).to_equal("i686")
```

</details>

#### x86_32 diagnostic has null base handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_x86_32_diagnostic()
expect(h.base.id).to_equal(0)
expect(h.base.is_null()).to_equal(true)
```

</details>

#### NeitherBackendFound diagnostic is not ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_neither_diagnostic()
expect(h.is_ok()).to_equal(false)
expect(h.error == Render2dX86InitError.NeitherBackendFound).to_equal(true)
expect(h.target_bits).to_equal(64)
```

</details>

#### ManagedShared session initialises with ref_count 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_cuda_session_managed()
expect(s.ref_count).to_equal(1)
expect(s.is_initialized).to_equal(true)
expect(s.mode == BackendSessionMode.ManagedShared).to_equal(true)
```

</details>

#### ManagedShared retain increments ref_count

1. s retain
   - Expected: s.ref_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_cuda_session_managed()
s.retain()
expect(s.ref_count).to_equal(2)
```

</details>

#### ManagedShared retain twice then release once leaves ref_count at 2

1. s retain
2. s retain
   - Expected: s.ref_count equals `3`
3. s release
   - Expected: s.ref_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_cuda_session_managed()
s.retain()
s.retain()
expect(s.ref_count).to_equal(3)
s.release()
expect(s.ref_count).to_equal(2)
```

</details>

#### ManagedShared session stays valid across multiple retains

1. s retain
2. s retain
   - Expected: s.is_valid() is true
   - Expected: s.ref_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_cuda_session_managed()
s.retain()
s.retain()
expect(s.is_valid()).to_equal(true)
expect(s.ref_count).to_equal(3)
```

</details>

#### release to zero makes session invalid

1. s release
   - Expected: s.ref_count equals `0`
   - Expected: s.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_cuda_session_managed()
s.release()
expect(s.ref_count).to_equal(0)
expect(s.is_valid()).to_equal(false)
```

</details>

#### uninitialised session is not valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_uninitialized_session()
expect(s.is_valid()).to_equal(false)
expect(s.is_initialized).to_equal(false)
```

</details>

#### sync_readback on uninitialised session returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_uninitialized_session()
val rc = s.sync_readback()
expect(rc).to_equal(1)
```

</details>

#### sync_readback on initialised session returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_cuda_session_managed()
val rc = s.sync_readback()
expect(rc).to_equal(0)
```

</details>

#### fill on session with host buf writes color to all pixels

1. s fill
   - Expected: s.host_buf[0] equals `0xFF0000FFu32`
   - Expected: s.host_buf[3] equals `0xFF0000FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_session_with_buf()
s.fill(0xFF0000FFu32)
expect(s.host_buf[0]).to_equal(0xFF0000FFu32)
expect(s.host_buf[3]).to_equal(0xFF0000FFu32)
```

</details>

#### fill on uninitialised session is a no-op

1. s fill
   - Expected: s.buf_w equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_uninitialized_session()
s.fill(0xFFFFFFFFu32)
expect(s.buf_w).to_equal(0)
```

</details>

#### session reports target_arch and target_bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_cuda_session_managed()
expect(s.target_arch).to_equal("x86_64")
expect(s.target_bits).to_equal(64)
```

</details>

#### session generation starts at 1 after init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = make_cuda_session_managed()
expect(s.generation).to_equal(1)
```

</details>

#### handle retain preserves mode and increments generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = make_cuda_base_handle()
val h2 = handle_retain_gen(h)
expect(h2.mode == BackendSessionMode.ManagedShared).to_equal(true)
expect(h2.generation).to_equal(1)
expect(h2.id).to_equal(100)
```

</details>

#### CUDA and Vulkan handles have distinct backend kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = make_cuda_handle_x86_64()
val vh = make_vulkan_handle_x86_64()
expect(ch.base.kind == BackendSessionKind.Cuda).to_equal(true)
expect(vh.base.kind == BackendSessionKind.Vulkan).to_equal(true)
expect(ch.base.kind == vh.base.kind).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/render_2d_x86_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Render2dX86Session

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
