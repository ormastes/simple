# Cuda Provider Smoke Specification

> <details>

<!-- sdn-diagram:id=cuda_provider_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cuda_provider_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cuda_provider_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cuda_provider_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Provider Smoke Specification

## Scenarios

### cuda_provider smoke

#### provider names are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_name(Provider.MockBackend)).to_equal("mock")
expect(provider_name(Provider.CpuBackend)).to_equal("cpu")
expect(provider_name(Provider.CudaBackend)).to_equal("cuda")
```

</details>

#### is_real_native is false for mock, true for cpu and cuda

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_is_real_native(Provider.MockBackend)).to_equal(false)
expect(provider_is_real_native(Provider.CpuBackend)).to_equal(true)
expect(provider_is_real_native(Provider.CudaBackend)).to_equal(true)
```

</details>

#### requires device memory only for cuda

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_requires_device_memory(Provider.MockBackend)).to_equal(false)
expect(provider_requires_device_memory(Provider.CpuBackend)).to_equal(false)
expect(provider_requires_device_memory(Provider.CudaBackend)).to_equal(true)
```

</details>

#### select_provider: mock when requested

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_name(select_provider("mock", true, true))).to_equal("mock")
```

</details>

#### select_provider: cuda when requested and available

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_name(select_provider("cuda", true, false))).to_equal("cuda")
```

</details>

#### select_provider: mock fallback when cuda requested but unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_name(select_provider("cuda", false, false))).to_equal("mock")
```

</details>

#### select_provider: cpu when openblas requested and available

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_name(select_provider("openblas", false, true))).to_equal("cpu")
```

</details>

#### select_provider: auto picks cuda first

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_name(select_provider("auto", true, true))).to_equal("cuda")
```

</details>

#### select_provider: auto picks cpu when cuda unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_name(select_provider("auto", false, true))).to_equal("cpu")
```

</details>

#### select_provider: auto falls back to mock

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_name(select_provider("auto", false, false))).to_equal("mock")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/cuda_provider_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cuda_provider smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
