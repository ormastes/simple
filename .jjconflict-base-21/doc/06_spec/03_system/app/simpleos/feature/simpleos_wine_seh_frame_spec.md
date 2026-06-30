# Simpleos Wine Seh Frame Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_seh_frame_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_seh_frame_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_seh_frame_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_seh_frame_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Seh Frame Specification

## Scenarios

### REQ-046: modeled SEH frame-chain dispatch

#### requires a mapped handler frame before SEH dispatch is planned

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
val frame = wine_seh_frame_new(77, 12, 0x701000, 0x403000, 0x700000, 0x710000)
val result = wine_seh_dispatch_fault(fault, [frame], 0x400000, 0x5000)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("seh-dispatch-planned")
expect(result.evidence).to_contain("seh-frame-chain-present")
expect(result.evidence).to_contain("seh-handler-mapped")
expect(result.evidence).to_contain("no-seh-handler-executed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_seh_frame_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-046: modeled SEH frame-chain dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
