# Resource Grant Specification

> 1. var bar = BarGrant request

<!-- sdn-diagram:id=resource_grant_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resource_grant_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resource_grant_spec -> std
resource_grant_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resource_grant_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resource Grant Specification

## Scenarios

### driver supervisor resource grants

#### rejects zero token BAR IRQ and DMA grants

1. var bar = BarGrant request
   - Expected: bar.grant(0, 0xFEB90000, 4096, true, false) equals `error: invalid token`
   - Expected: bar.has_issued_token() is false
   - Expected: bar.grant(10, 0xFEB90000, 0, true, false) equals `error: invalid size`
   - Expected: bar.grant(10, 0xFEB90000, 4096, true, false) equals `ok`
   - Expected: bar.has_issued_token() is true
2. var irq = IrqGrant request legacy
   - Expected: irq.grant(0) equals `error: invalid token`
   - Expected: irq.has_issued_token() is false
   - Expected: irq.grant(11) equals `ok`
   - Expected: irq.has_issued_token() is true
3. var dma = DmaGrant request
   - Expected: dma.grant(0, 0x100000, 0x200000) equals `error: invalid token`
   - Expected: dma.has_issued_token() is false
   - Expected: dma.grant(12, 0x100000, 0x200000) equals `ok`
   - Expected: dma.has_issued_token() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bar = BarGrant.request(0, 2, 0, 0)
expect(bar.grant(0, 0xFEB90000, 4096, true, false)).to_equal("error: invalid token")
expect(bar.has_issued_token()).to_equal(false)
expect(bar.grant(10, 0xFEB90000, 0, true, false)).to_equal("error: invalid size")
expect(bar.grant(10, 0xFEB90000, 4096, true, false)).to_equal("ok")
expect(bar.has_issued_token()).to_equal(true)

var irq = IrqGrant.request_legacy(11, 42)
expect(irq.grant(0)).to_equal("error: invalid token")
expect(irq.has_issued_token()).to_equal(false)
expect(irq.grant(11)).to_equal("ok")
expect(irq.has_issued_token()).to_equal(true)

var dma = DmaGrant.request(8192, "bidirectional", 7)
expect(dma.grant(0, 0x100000, 0x200000)).to_equal("error: invalid token")
expect(dma.has_issued_token()).to_equal(false)
expect(dma.grant(12, 0x100000, 0x200000)).to_equal("ok")
expect(dma.has_issued_token()).to_equal(true)
```

</details>

#### does not grant a resource set from a placeholder base token

1. var grants = ResourceGrantSet create
   - Expected: grants.add_bar(0) equals `added bar slot 0`
   - Expected: grants.add_irq(11) equals `added irq slot 0`
   - Expected: grants.add_dma(8192) equals `added dma slot 0`
   - Expected: grants.grant_all(0) equals `0`
   - Expected: grants.all_granted_with_tokens() is false
   - Expected: grants.grant_all(100) equals `3`
   - Expected: grants.all_granted_with_tokens() is true
   - Expected: grants.b0_token equals `100`
   - Expected: grants.i0_token equals `101`
   - Expected: grants.d0_token equals `102`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var grants = ResourceGrantSet.create("nvme-user", 77)
expect(grants.add_bar(0)).to_equal("added bar slot 0")
expect(grants.add_irq(11)).to_equal("added irq slot 0")
expect(grants.add_dma(8192)).to_equal("added dma slot 0")
expect(grants.grant_all(0)).to_equal(0)
expect(grants.all_granted_with_tokens()).to_equal(false)

expect(grants.grant_all(100)).to_equal(3)
expect(grants.all_granted_with_tokens()).to_equal(true)
expect(grants.b0_token).to_equal(100)
expect(grants.i0_token).to_equal(101)
expect(grants.d0_token).to_equal(102)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/driver_supervisor/resource_grant_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- driver supervisor resource grants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
