# Graphics 3d Session Managed Backend Specification

> <details>

<!-- sdn-diagram:id=graphics_3d_session_managed_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=graphics_3d_session_managed_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

graphics_3d_session_managed_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=graphics_3d_session_managed_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graphics 3d Session Managed Backend Specification

## Scenarios

### BackendSessionHandle

#### invalid handle has id -1 and valid false

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BackendSessionHandle.invalid()
expect(h.id).to_equal(-1)
expect(h.valid == false).to_equal(true)
```

</details>

#### create handle has id >= 0 and valid true

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BackendSessionHandle.create(101, "cpu", "managed_shared")
expect(h.id).to_equal(101)
expect(h.valid).to_equal(true)
```

</details>

#### is_valid returns false for invalid handle

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BackendSessionHandle.invalid()
expect(BackendSessionHandle.is_valid(h) == false).to_equal(true)
```

</details>

#### is_valid returns true for created handle

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BackendSessionHandle.create(42, "vulkan", "managed_shared")
expect(BackendSessionHandle.is_valid(h)).to_equal(true)
```

</details>

#### increment_generation increases generation by 1

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BackendSessionHandle.create(10, "cpu", "managed_shared")
val h2 = BackendSessionHandle.increment_generation(h)
expect(h2.generation).to_equal(2)
```

</details>

### BackendSessionPolicy

#### default_managed mode is managed_shared

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.default_managed()
expect(p.mode).to_equal("managed_shared")
```

</details>

#### perf_exclusive policy has allow_fallback false

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.perf_exclusive()
expect(p.allow_fallback == false).to_equal(true)
```

</details>

#### legacy_no_session policy has perf_counters_enabled false

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.legacy_no_session()
expect(p.perf_counters_enabled == false).to_equal(true)
```

</details>

#### perf_exclusive has allow_readback true

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.perf_exclusive()
expect(p.allow_readback).to_equal(true)
```

</details>

### Session API

#### backend_session_create with empty kind returns invalid

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.default_managed()
val h = backend_session_create("", p, 1)
expect(BackendSessionHandle.is_valid(h) == false).to_equal(true)
```

</details>

#### backend_session_create with cpu kind returns valid handle

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.default_managed()
val h = backend_session_create("cpu", p, 1)
expect(BackendSessionHandle.is_valid(h)).to_equal(true)
```

</details>

#### backend_session_retain increments generation

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.default_managed()
val h = backend_session_create("cpu", p, 1)
val h2 = backend_session_retain(h)
expect(h2.generation).to_equal(2)
```

</details>

#### backend_session_retain perf_exclusive returns invalid

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.perf_exclusive()
val h = backend_session_create("vulkan", p, 1)
val h2 = backend_session_retain(h)
expect(BackendSessionHandle.is_valid(h2) == false).to_equal(true)
```

</details>

#### backend_session_release returns invalid handle

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.default_managed()
val h = backend_session_create("cpu", p, 1)
val released = backend_session_release(h)
expect(BackendSessionHandle.is_valid(released) == false).to_equal(true)
```

</details>

### BackendFrame lifecycle

#### begin_frame on valid session sets is_active true

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.default_managed()
val h = backend_session_create("cpu", p, 1)
val frm = backend_session_begin_frame(h, 0, 1920, 1080, false)
expect(frm.is_active).to_equal(true)
```

</details>

#### begin_frame on invalid session returns inactive frame

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BackendSessionHandle.invalid()
val frm = backend_session_begin_frame(h, 0, 1920, 1080, false)
expect(frm.is_active == false).to_equal(true)
```

</details>

#### end_frame returns valid stats with correct session_id

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.default_managed()
val h = backend_session_create("cpu", p, 1)
val frm = backend_session_begin_frame(h, 0, 800, 600, false)
val stats = backend_session_end_frame(frm)
expect(stats.valid).to_equal(true)
expect(stats.session_id).to_equal(h.id)
```

</details>

#### sync_readback returns empty when allow_readback false

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.default_managed()
val h = backend_session_create("cpu", p, 1)
val frm = backend_session_begin_frame(h, 0, 100, 100, false)
val bytes = backend_session_sync_readback(frm)
expect(bytes.length).to_equal(0)
```

</details>

#### sync_readback returns 4 bytes when allow_readback true

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = BackendSessionPolicy.perf_exclusive()
val h = backend_session_create("cpu", p, 1)
val frm = backend_session_begin_frame(h, 0, 100, 100, true)
val bytes = backend_session_sync_readback(frm)
expect(bytes.length).to_equal(4)
```

</details>

### RenderBackendPerf

#### perf counters start at zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val perf = RenderBackendPerf.create_for_mode(1, "managed_shared")
val c = perf.counters
expect(c.total_frames).to_equal(0)
expect(c.sample_count).to_equal(0)
```

</details>

#### record_frame increments total_frames

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val perf = RenderBackendPerf.create_for_mode(1, "managed_shared")
val perf2 = RenderBackendPerf.record_frame(perf, 16, 100)
expect(perf2.counters.total_frames).to_equal(1)
```

</details>

#### reset_counters brings total_frames back to zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val perf = RenderBackendPerf.create_for_mode(1, "managed_shared")
val perf2 = RenderBackendPerf.record_frame(perf, 16, 100)
val perf3 = RenderBackendPerf.reset_counters(perf2)
expect(perf3.counters.total_frames).to_equal(0)
```

</details>

#### backend_mode returns mode text

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val perf = RenderBackendPerf.create_for_mode(5, "perf_exclusive")
expect(RenderBackendPerf.backend_mode(perf)).to_equal("perf_exclusive")
```

</details>

#### get_session_id returns session_id

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val perf = RenderBackendPerf.create_for_mode(42, "managed_shared")
expect(RenderBackendPerf.get_session_id(perf)).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/graphics_3d_session_managed_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BackendSessionHandle
- BackendSessionPolicy
- Session API
- BackendFrame lifecycle
- RenderBackendPerf

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
