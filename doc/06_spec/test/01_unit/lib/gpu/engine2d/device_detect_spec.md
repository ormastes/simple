# Device Detect Specification

> <details>

<!-- sdn-diagram:id=device_detect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=device_detect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

device_detect_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=device_detect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Device Detect Specification

## Scenarios

### GpuBackend

#### AC-5: has Qualcomm variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-1: has Vulkan variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-2: has Cuda variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-3: has Rocm variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: has OneApi variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### has None_ variant for CPU fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### detect_backends_full

#### AC-8: accepts GpuFfiMode parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-8: Static mode checks extern fn availability

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-8: Dynamic mode checks dlopen availability

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-1: Vulkan detection enabled (not commented out)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-3: ROCm detection enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: Intel detection enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### detect_best_backend_for_platform

#### AC-7: returns a valid backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

<details>
<summary>Advanced: AC-7: priority order matches platform matrix</summary>

#### AC-7: priority order matches platform matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/device_detect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GpuBackend
- detect_backends_full
- detect_best_backend_for_platform

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
