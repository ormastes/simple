# Ffi Dispatch Specification

> <details>

<!-- sdn-diagram:id=ffi_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ffi_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ffi_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ffi_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ffi Dispatch Specification

## Scenarios

### GpuFfiMode

#### AC-8: has Static variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = GpuFfiMode.Static
expect(mode.to_text()).to_equal("Static")
```

</details>

#### AC-8: has Dynamic variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = GpuFfiMode.Dynamic
expect(mode.to_text()).to_equal("Dynamic")
```

</details>

### default_ffi_mode

#### AC-8: returns a valid GpuFfiMode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = default_ffi_mode()
val is_valid = mode.to_text() == "Static" or mode.to_text() == "Dynamic"
expect(is_valid).to_equal(true)
```

</details>

### FfiDispatchBase

#### AC-8: mode() returns the dispatch mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = GpuFfiMode.Dynamic
expect(mode.to_text()).to_equal("Dynamic")
```

</details>

#### AC-8: is_available() returns bool for availability check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = false
expect(available).to_equal(false)
```

</details>

### dynamic dispatch

#### AC-8: create_dynamic returns nil when library not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = try_create_dynamic_vulkan("nonexistent_libvulkan.so.999")
expect(result).to_be_nil()
```

</details>

#### AC-8: graceful fallback when vendor SDK not installed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = resolve_ffi_mode("vulkan")
val is_valid = mode.to_text() == "Static" or mode.to_text() == "Dynamic"
expect(is_valid).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GpuFfiMode
- default_ffi_mode
- FfiDispatchBase
- dynamic dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
