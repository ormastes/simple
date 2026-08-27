# Driver Acceleration Perf Specification

> Tests covering SimpleOS driver acceleration performance report.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Acceleration Perf Specification

## Scenarios

### SimpleOS driver acceleration performance report

#### compares buffered copy with aligned direct DMA on the same payload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compares buffered copy with aligned direct DMA on the same payload
   - Expected: buffered_file_copy_bytes(payload) equals `4096`
   - Expected: direct_dma_copy_bytes(payload, true, true) equals `0`
   - Expected: direct_dma_copy_bytes(payload, false, true) equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares buffered copy with aligned direct DMA on the same payload")
val payload = 4096u64
expect(buffered_file_copy_bytes(payload)).to_equal(4096)
expect(direct_dma_copy_bytes(payload, true, true)).to_equal(0)
expect(direct_dma_copy_bytes(payload, false, true)).to_equal(4096)
```

</details>

#### compares full-frame and dirty-rectangle display flush cost

- compares full-frame and dirty-rectangle display flush cost
   - Expected: full equals `3145728`
   - Expected: dirty equals `8192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares full-frame and dirty-rectangle display flush cost")
val full = full_frame_flush_bytes(1024, 768, 4)
val dirty = dirty_rect_flush_bytes(1024, 768, 16, 32, 64, 32, 4)
expect(full).to_equal(3145728)
expect(dirty).to_equal(8192)
expect(full).to_be_greater_than(dirty)
```

</details>

#### records backend capability, isolation mode, and RSS fields

- records backend capability, isolation mode, and RSS fields
   - Expected: report.backend_kind equals `virtio-gpu-dma`
   - Expected: report.isolation_mode equals `trusted-driver/no-iommu`
   - Expected: report.network_descriptor_compatible is true
   - Expected: report.buffered_copy_bytes equals `4096`
   - Expected: report.direct_dma_copy_bytes equals `0`
   - Expected: report.dirty_rect_flush_bytes equals `8192`
   - Expected: report.max_rss_kib equals `65536`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records backend capability, isolation mode, and RSS fields")
val report = build_driver_acceleration_report(
    "virtio-gpu-dma",
    "trusted-driver/no-iommu",
    true,
    4096,
    true,
    true,
    1024,
    768,
    16,
    32,
    64,
    32,
    240,
    104857600,
    65536
)
expect(report.backend_kind).to_equal("virtio-gpu-dma")
expect(report.isolation_mode).to_equal("trusted-driver/no-iommu")
expect(report.network_descriptor_compatible).to_equal(true)
expect(report.buffered_copy_bytes).to_equal(4096)
expect(report.direct_dma_copy_bytes).to_equal(0)
expect(report.dirty_rect_flush_bytes).to_equal(8192)
expect(report.max_rss_kib).to_equal(65536)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos/driver_acceleration_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS driver acceleration performance report.
- SimpleOS driver acceleration performance report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `2c0501f47a9b11f43677ac0ae1aade7257304743f2f8a63746c44f4f4b54d9cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c0501f47a9b11f43677ac0ae1aade7257304743f2f8a63746c44f4f4b54d9cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c0501f47a9b11f43677ac0ae1aade7257304743f2f8a63746c44f4f4b54d9cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/os/simpleos/driver_acceleration_perf_spec.spl
mirror: doc/06_spec/03_system/os/simpleos/driver_acceleration_perf_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos/driver_acceleration_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos/driver_acceleration_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos/driver_acceleration_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/simpleos/driver_acceleration_perf_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares buffered copy with aligned direct DMA on the same payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/driver_acceleration_perf_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares full-frame and dirty-rectangle display flush cost' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/driver_acceleration_perf_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records backend capability, isolation mode, and RSS fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
