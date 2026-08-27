# Net Shared Dma Ownership Specification

> Tests covering FR-NET-0008 shared DMA buffer ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Shared Dma Ownership Specification

## Scenarios

### FR-NET-0008 shared DMA buffer ownership

#### driver handoff

#### uses SharedDmaBuffer for network packet leases and file direct I/O

- uses SharedDmaBuffer for network packet leases and file direct I/O
   - Expected: rx.buffer.allocation_id equals `77`
   - Expected: tx.buffer.len() equals `1024`
   - Expected: ext.validate_shared_buffer(1024, dma).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses SharedDmaBuffer for network packet leases and file direct I/O")
val dma = make_dma(4, DmaCachePolicy.FlushRequired, 77)
val rx = packet_rx_dma_lease(1u64, dma)
val tx = packet_tx_dma_lease(1u64, dma)
val ext = DirectIoExt(
    sector_alignment: 512,
    file_alignment: 512,
    max_io_bytes: 4096,
    backend_tag: "virtio-blk",
    bounce_allowed: false)
expect(rx.buffer.allocation_id).to_equal(77)
expect(tx.buffer.len()).to_equal(1024)
expect(ext.validate_shared_buffer(1024, dma).is_ok()).to_equal(true)
```

</details>

#### represents display transfer buffers with the same shared descriptor

- represents display transfer buffers with the same shared descriptor
   - Expected: display.cpu_addr() equals `0x1000`
   - Expected: display.phys_addr() equals `0x2000`
   - Expected: display.device_visible_addr() equals `0x2000`
   - Expected: display.matches_bdf(0, 2, 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("represents display transfer buffers with the same shared descriptor")
val display = make_dma(2, DmaCachePolicy.WriteCombining, 77)
expect(display.cpu_addr()).to_equal(0x1000)
expect(display.phys_addr()).to_equal(0x2000)
expect(display.device_visible_addr()).to_equal(0x2000)
expect(display.matches_bdf(0, 2, 0)).to_equal(true)
```

</details>

#### release and cache policy

#### rejects double-free and wrong-size release through the shared contract

- rejects double-free and wrong-size release through the shared contract
   - Expected: validate_shared_dma_release(dma, release_req(4, 1024, false)).is_ok() is true
   - Expected: validate_shared_dma_release(dma, release_req(4, 1024, true)).is_err() is true
   - Expected: validate_shared_dma_release(dma, release_req(4, 512, false)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects double-free and wrong-size release through the shared contract")
val dma = make_dma(4, DmaCachePolicy.Coherent, 77)
expect(validate_shared_dma_release(dma, release_req(4, 1024, false)).is_ok()).to_equal(true)
expect(validate_shared_dma_release(dma, release_req(4, 1024, true)).is_err()).to_equal(true)
expect(validate_shared_dma_release(dma, release_req(4, 512, false)).is_err()).to_equal(true)
```

</details>

#### keeps cache maintenance explicit during packet completion

- keeps cache maintenance explicit during packet completion
   - Expected: done.owner equals `driver`
   - Expected: done.completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps cache maintenance explicit during packet completion")
val dma = make_dma(4, DmaCachePolicy.FlushRequired, 77)
val rx = packet_rx_dma_lease(1u64, dma)
dma_shared_sync_cpu_to_device(rx.buffer)
dma_shared_sync_device_to_cpu(rx.buffer)
val done = packet_dma_complete(rx)
expect(done.owner).to_equal("driver")
expect(done.completed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_shared_dma_ownership_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-NET-0008 shared DMA buffer ownership.
- FR-NET-0008 shared DMA buffer ownership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `88b8e8e156d6ba1d4ac1d3dd4ce3f1e35cc00976065bb01c9dbdf176d142e24e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88b8e8e156d6ba1d4ac1d3dd4ce3f1e35cc00976065bb01c9dbdf176d142e24e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88b8e8e156d6ba1d4ac1d3dd4ce3f1e35cc00976065bb01c9dbdf176d142e24e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/net_shared_dma_ownership_spec.spl
mirror: doc/06_spec/03_system/os/net_shared_dma_ownership_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/net_shared_dma_ownership_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/net_shared_dma_ownership_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/net_shared_dma_ownership_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/net_shared_dma_ownership_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses SharedDmaBuffer for network packet leases and file direct I/O' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_shared_dma_ownership_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'represents display transfer buffers with the same shared descriptor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_shared_dma_ownership_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects double-free and wrong-size release through the shared contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
