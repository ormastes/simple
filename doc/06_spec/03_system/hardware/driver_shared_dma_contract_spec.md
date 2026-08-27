# Driver Shared Dma Contract Specification

> Tests covering FR-DRIVER-0009 shared DMA descriptor contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Shared Dma Contract Specification

## Scenarios

### FR-DRIVER-0009 shared DMA descriptor contract

#### canonical descriptor fields

#### network, file, and display consumers use the same descriptor shape

- network, file, and display consumers use the same descriptor shape
   - Expected: network_rx.cpu_addr() equals `file_direct.cpu_addr()`
   - Expected: network_rx.phys_addr() equals `file_direct.phys_addr()`
   - Expected: display_transfer.device_visible_addr() equals `0x2000`
   - Expected: network_rx.matches_bdf(0, 1, 0) is true
   - Expected: file_direct.matches_bdf(0, 2, 0) is true
   - Expected: display_transfer.matches_bdf(0, 3, 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("network, file, and display consumers use the same descriptor shape")
val network_rx = make_desc(DmaCachePolicy.FlushRequired, 1, 11)
val file_direct = make_desc(DmaCachePolicy.Uncached, 2, 12)
val display_transfer = make_desc(DmaCachePolicy.WriteCombining, 3, 13)
expect(network_rx.cpu_addr()).to_equal(file_direct.cpu_addr())
expect(network_rx.phys_addr()).to_equal(file_direct.phys_addr())
expect(display_transfer.device_visible_addr()).to_equal(0x2000)
expect(network_rx.matches_bdf(0, 1, 0)).to_equal(true)
expect(file_direct.matches_bdf(0, 2, 0)).to_equal(true)
expect(display_transfer.matches_bdf(0, 3, 0)).to_equal(true)
```

</details>

#### all explicit cache policy variants remain representable

- all explicit cache policy variants remain representable
   - Expected: coherent.is_valid() is true
   - Expected: flush_required.is_valid() is true
   - Expected: uncached.is_valid() is true
   - Expected: write_combining.is_valid() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all explicit cache policy variants remain representable")
val coherent = make_desc(DmaCachePolicy.Coherent, 4, 20)
val flush_required = make_desc(DmaCachePolicy.FlushRequired, 4, 21)
val uncached = make_desc(DmaCachePolicy.Uncached, 4, 22)
val write_combining = make_desc(DmaCachePolicy.WriteCombining, 4, 23)
dma_shared_sync_cpu_to_device(coherent)
dma_shared_sync_device_to_cpu(flush_required)
expect(coherent.is_valid()).to_equal(true)
expect(flush_required.is_valid()).to_equal(true)
expect(uncached.is_valid()).to_equal(true)
expect(write_combining.is_valid()).to_equal(true)
```

</details>

#### release authority

#### accepts release only for matching task, BDF, size, and allocation id

- accepts release only for matching task, BDF, size, and allocation id
   - Expected: validate_shared_dma_release(desc, req).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts release only for matching task, BDF, size, and allocation id")
val desc = make_desc(DmaCachePolicy.Coherent, 5, 30)
val req = make_release(1024, 7, 5, 30, false)
expect(validate_shared_dma_release(desc, req).is_ok()).to_equal(true)
```

</details>

#### rejects double-free, wrong-size free, and wrong-owner free

- rejects double-free, wrong-size free, and wrong-owner free
   - Expected: validate_shared_dma_release(desc, make_release(1024, 7, 5, 30, true)).is_err() is true
   - Expected: validate_shared_dma_release(desc, make_release(512, 7, 5, 30, false)).is_err() is true
   - Expected: validate_shared_dma_release(desc, make_release(1024, 8, 5, 30, false)).is_err() is true
   - Expected: validate_shared_dma_release(desc, make_release(1024, 7, 6, 30, false)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects double-free, wrong-size free, and wrong-owner free")
val desc = make_desc(DmaCachePolicy.Coherent, 5, 30)
expect(validate_shared_dma_release(desc, make_release(1024, 7, 5, 30, true)).is_err()).to_equal(true)
expect(validate_shared_dma_release(desc, make_release(512, 7, 5, 30, false)).is_err()).to_equal(true)
expect(validate_shared_dma_release(desc, make_release(1024, 8, 5, 30, false)).is_err()).to_equal(true)
expect(validate_shared_dma_release(desc, make_release(1024, 7, 6, 30, false)).is_err()).to_equal(true)
```

</details>

#### file direct I/O

#### validates std.io.dma.SharedDmaBuffer directly for block/file DMA

- validates std.io.dma.SharedDmaBuffer directly for block/file DMA
   - Expected: ext.validate_shared_buffer(1024, desc).is_ok() is true
   - Expected: ext.validate_shared_buffer(7, desc).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates std.io.dma.SharedDmaBuffer directly for block/file DMA")
val ext = DirectIoExt(
    sector_alignment: 512,
    file_alignment: 512,
    max_io_bytes: 4096,
    backend_tag: "virtio-blk",
    bounce_allowed: false)
val desc = make_desc(DmaCachePolicy.Uncached, 2, 40)
expect(ext.validate_shared_buffer(1024, desc).is_ok()).to_equal(true)
expect(ext.validate_shared_buffer(7, desc).is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/driver_shared_dma_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-DRIVER-0009 shared DMA descriptor contract.
- FR-DRIVER-0009 shared DMA descriptor contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea71be35683ea2fe6261c98df4ba79cc407aa506e1b8db18ee67ec719492c283`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea71be35683ea2fe6261c98df4ba79cc407aa506e1b8db18ee67ec719492c283`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea71be35683ea2fe6261c98df4ba79cc407aa506e1b8db18ee67ec719492c283`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/hardware/driver_shared_dma_contract_spec.spl
mirror: doc/06_spec/03_system/hardware/driver_shared_dma_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/driver_shared_dma_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/driver_shared_dma_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/driver_shared_dma_contract_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'network, file, and display consumers use the same descriptor shape' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/driver_shared_dma_contract_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all explicit cache policy variants remain representable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/driver_shared_dma_contract_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts release only for matching task, BDF, size, and allocation id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
