# Rdma Specification

> <details>

<!-- sdn-diagram:id=rdma_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rdma_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rdma_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rdma_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rdma Specification

## Scenarios

### RDMA provider hardware evidence

#### rejects model and host SFFI modes as hardware RDMA

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = rdma_provider_evidence(
    "model",
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "resource-grant-set:tok=41",
    "non-secure-resource-namespace"
)
val host = rdma_provider_evidence(
    "sffi-host",
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "resource-grant-set:tok=42",
    "non-secure-resource-namespace"
)

expect(rdma_provider_readiness_reason(model)).to_equal("rdma-not-hardware:model")
expect(rdma_provider_readiness_reason(host)).to_equal("rdma-not-hardware:sffi-host")
```

</details>

#### requires an issued grant token and non-secure namespace for device mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_token = rdma_provider_evidence(
    "device",
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "resource-grant-set",
    "non-secure-resource-namespace"
)
val bad_namespace = rdma_provider_evidence(
    "device",
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "resource-grant-set:tok=43",
    "secure-kernel-namespace"
)

expect(rdma_provider_hardware_ready(no_token)).to_equal(false)
expect(rdma_provider_readiness_reason(no_token)).to_equal("missing-rdma-issued-grant-token:resource-grant-set")
expect(rdma_provider_readiness_reason(bad_namespace)).to_equal("missing-rdma-non-secure-namespace:secure-kernel-namespace")
```

</details>

#### accepts device mode only with full PCI DMA grant and namespace evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = rdma_provider_evidence(
    "device",
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "resource-grant-set:tok=44",
    "non-secure-resource-namespace"
)

expect(rdma_provider_readiness_reason(ready)).to_equal("ready")
expect(rdma_provider_hardware_ready(ready)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/io/rdma_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RDMA provider hardware evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
