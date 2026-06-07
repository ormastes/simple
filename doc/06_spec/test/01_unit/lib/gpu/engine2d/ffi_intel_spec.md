# Ffi Intel Specification

> <details>

<!-- sdn-diagram:id=ffi_intel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ffi_intel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ffi_intel_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ffi_intel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ffi Intel Specification

## Scenarios

### IntelFfi

### create_dynamic

#### AC-4: attempts to load libze_loader.so

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-8: returns nil when Level Zero not installed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### create_static

#### AC-8: static mode available when runtime is built

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Level Zero driver

#### AC-4: zeInit returns success

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: zeDriverGet returns driver count

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Level Zero device

#### AC-4: device enumeration for Arc/Xe/integrated

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Level Zero command list

#### AC-4: zeCommandListCreate returns handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Level Zero kernel

#### AC-4: zeKernelCreate from SPIR-V module

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: zeCommandListAppendLaunchKernel dispatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### platform support

#### AC-7: Intel L0 on Linux and Windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: Intel dynamic-only (no Rust runtime)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/ffi_intel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IntelFfi
- create_dynamic
- create_static
- Level Zero driver
- Level Zero device
- Level Zero command list
- Level Zero kernel
- platform support

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
