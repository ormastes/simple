# Src Dl Facade Specification

> <details>

<!-- sdn-diagram:id=src_dl_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=src_dl_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

src_dl_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=src_dl_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Src Dl Facade Specification

## Scenarios

### gc_async_mut src dl facade

#### re-exports DL config, device, dtype, and backend helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DType.F32.size_bytes()).to_equal(4)
expect(DType.F16.is_float()).to_equal(true)
expect(DType.U8.is_signed()).to_equal(false)
expect(Backend.PyTorch.to_string()).to_equal("torch")

val cfg = DLConfig.default()
expect(cfg.default_dtype).to_equal(DType.F32)
expect(cfg.default_device.is_cpu()).to_equal(true)

expect(cpu().is_cpu()).to_equal(true)
expect(cuda(1).is_gpu()).to_equal(true)
expect(default_gpu().is_gpu()).to_equal(true)
expect(parse_device("cuda:1").is_gpu()).to_equal(true)
expect(parse_dtype("bf16")).to_equal(DType.BF16)
expect(parse_backend("native")).to_equal(Backend.Native)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/src/dl/src_dl_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut src dl facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
