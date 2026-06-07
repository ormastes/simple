# Wine Seh Frame Specification

> <details>

<!-- sdn-diagram:id=wine_seh_frame_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_seh_frame_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_seh_frame_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_seh_frame_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Seh Frame Specification

## Scenarios

### Wine SEH frame-chain planner

#### plans SEH dispatch when a thread frame and mapped handler exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
val frame = wine_seh_frame_new(77, 12, 0x701000, 0x403000, 0x700000, 0x710000)
val result = wine_seh_dispatch_fault(fault, [frame], 0x400000, 0x5000)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("seh-dispatch-planned")
expect(result.handler_address).to_equal(0x403000)
expect(result.frame_count).to_equal(1)
expect(result.evidence).to_contain("seh-frame-chain-present")
expect(result.evidence).to_contain("seh-handler-mapped")
expect(result.evidence).to_contain("no-seh-handler-executed")
```

</details>

#### rejects frame handlers outside the mapped image

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
val frame = wine_seh_frame_new(77, 12, 0x701000, 0x500000, 0x700000, 0x710000)
val result = wine_seh_dispatch_fault(fault, [frame], 0x400000, 0x5000)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("seh-handler-unmapped")
expect(result.evidence).to_contain("seh-dispatch-blocked")
```

</details>

#### rejects non-SEH fault policies before handler handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "terminate-process")
val frame = wine_seh_frame_new(77, 12, 0x701000, 0x403000, 0x700000, 0x710000)
val result = wine_seh_dispatch_fault(fault, [frame], 0x400000, 0x5000)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("seh-policy:terminate-process")
expect(result.frame_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_seh_frame_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine SEH frame-chain planner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
