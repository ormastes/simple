# Grant Broker Specification

> 1. var broker = GrantBroker create

<!-- sdn-diagram:id=grant_broker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=grant_broker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

grant_broker_spec -> std
grant_broker_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=grant_broker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Grant Broker Specification

## Scenarios

### driver supervisor grant broker

#### does not issue grants when the broker token cursor is invalid

1. var broker = GrantBroker create
   - Expected: broker.register_driver("nvme-user", 42) equals ``
   - Expected: broker.grant_bar("nvme-user", 0) equals `0`
   - Expected: broker.grant_irq("nvme-user", 11) equals `0`
   - Expected: broker.grant_dma("nvme-user", 8192) equals `0`
   - Expected: broker.g0_bar_count equals `0`
   - Expected: broker.g0_irq_count equals `0`
   - Expected: broker.g0_dma_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var broker = GrantBroker.create()
expect(broker.register_driver("nvme-user", 42)).to_equal("")
broker.next_token = 0
expect(broker.grant_bar("nvme-user", 0)).to_equal(0)
expect(broker.grant_irq("nvme-user", 11)).to_equal(0)
expect(broker.grant_dma("nvme-user", 8192)).to_equal(0)
expect(broker.g0_bar_count).to_equal(0)
expect(broker.g0_irq_count).to_equal(0)
expect(broker.g0_dma_count).to_equal(0)
```

</details>

#### rejects raw passthrough without issued broker tokens

1. var grant = RawDeviceGrant request
   - Expected: grant.grant_passthrough(0) equals `error: invalid broker token`
   - Expected: grant.has_issued_tokens() is false
   - Expected: grant.grant_passthrough(30) equals `passthrough granted tok=30`
   - Expected: grant.has_issued_tokens() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var grant = RawDeviceGrant.request(0, 2, 0, 77)
expect(grant.grant_passthrough(0)).to_equal("error: invalid broker token")
expect(grant.has_issued_tokens()).to_equal(false)
expect(grant.grant_passthrough(30)).to_equal("passthrough granted tok=30")
expect(grant.has_issued_tokens()).to_equal(true)
```

</details>

#### requires a positive broker token for exokernel lane readiness

1. var lane = ExokernelLaneStatus create
   - Expected: lane.is_ready() is false
   - Expected: lane.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lane = ExokernelLaneStatus.create()
lane.has_contract = true
lane.has_tests = true
lane.has_docs = true
lane.has_reviewer = true
lane.bar_ready = true
lane.irq_ready = true
lane.dma_ready = true
lane.iommu_ready = true
lane.broker_ready = true
lane.broker_token = 0
expect(lane.is_ready()).to_equal(false)
expect(lane.report()).to_contain("broker_tok=0")
lane.broker_token = 30
expect(lane.is_ready()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/driver_supervisor/grant_broker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- driver supervisor grant broker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
