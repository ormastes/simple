# Driver Dma Direct Io Specification

> Tests covering FR-DRIVER-0010 DMA-backed file and block direct I/O.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Dma Direct Io Specification

## Scenarios

### FR-DRIVER-0010 DMA-backed file and block direct I/O

#### explicit direct I/O requests

#### submits aligned reads without buffered copy bytes

- submits aligned reads without buffered copy bytes
   - Expected: req.op equals `DIRECT_IO_READ`
   - Expected: result.submitted is true
   - Expected: result.bytes equals `1024u64`
   - Expected: result.backend_tag equals `nvme`
   - Expected: result.status equals `submitted`
   - Expected: result.buffered_copy_bytes equals `0u64`
   - Expected: result.direct_dma_copy_bytes equals `0u64`
   - Expected: result.cleanup_required is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("submits aligned reads without buffered copy bytes")
val buf = dma(1024u64, 0x2000u64, 7u64)
val req = direct_io_read_request(1u64, 1024, buf, 100u32)
expect(req.op).to_equal(DIRECT_IO_READ)
match direct_io_submit(make_direct_ext(false), req):
    Ok(result):
        expect(result.submitted).to_equal(true)
        expect(result.bytes).to_equal(1024u64)
        expect(result.backend_tag).to_equal("nvme")
        expect(result.status).to_equal("submitted")
        expect(result.buffered_copy_bytes).to_equal(0u64)
        expect(result.direct_dma_copy_bytes).to_equal(0u64)
        expect(result.cleanup_required).to_equal(true)
    Err(_): expect(false).to_equal(true)
```

</details>

#### submits aligned writes with explicit DMA sync semantics

- submits aligned writes with explicit DMA sync semantics
   - Expected: req.op equals `DIRECT_IO_WRITE`
   - Expected: result.status equals `submitted`
   - Expected: result.bytes equals `512u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("submits aligned writes with explicit DMA sync semantics")
val buf = dma(512u64, 0x3000u64, 8u64)
val req = direct_io_write_request(1u64, 0, buf, 100u32)
expect(req.op).to_equal(DIRECT_IO_WRITE)
match direct_io_submit(make_direct_ext(false), req):
    Ok(result):
        expect(result.status).to_equal("submitted")
        expect(result.bytes).to_equal(512u64)
    Err(_): expect(false).to_equal(true)
```

</details>

#### alignment and fallback

#### rejects unaligned direct I/O when bounce buffering is disabled

- rejects unaligned direct I/O when bounce buffering is disabled
   - Expected: direct_io_submit(make_direct_ext(false), req).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects unaligned direct I/O when bounce buffering is disabled")
val buf = dma(1024u64, 0x2000u64, 9u64)
val req = direct_io_read_request(1u64, 7, buf, 100u32)
expect(direct_io_submit(make_direct_ext(false), req).is_err()).to_equal(true)
```

</details>

#### routes unaligned direct I/O through an explicit bounce result when enabled

- routes unaligned direct I/O through an explicit bounce result when enabled
   - Expected: result.status equals `bounce-buffered`
   - Expected: result.buffered_copy_bytes equals `1024u64`
   - Expected: result.direct_dma_copy_bytes equals `1024u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes unaligned direct I/O through an explicit bounce result when enabled")
val buf = dma(1024u64, 0x2000u64, 10u64)
val req = direct_io_write_request(1u64, 7, buf, 100u32)
match direct_io_submit(make_direct_ext(true), req):
    Ok(result):
        expect(result.status).to_equal("bounce-buffered")
        expect(result.buffered_copy_bytes).to_equal(1024u64)
        expect(result.direct_dma_copy_bytes).to_equal(1024u64)
    Err(_): expect(false).to_equal(true)
```

</details>

#### timeout and cleanup

#### reports bounded timeout as a transient direct I/O error

- reports bounded timeout as a transient direct I/O error


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports bounded timeout as a transient direct I/O error")
val buf = dma(512u64, 0x4000u64, 11u64)
val req = direct_io_read_request(1u64, 0, buf, 0u32)
match direct_io_submit(make_direct_ext(false), req):
    Ok(_): expect(false).to_equal(true)
    Err(err):
        match err:
            case Transient(code): expect(code).to_equal(DIRECT_IO_TIMEOUT_CODE)
            case _: expect(false).to_equal(true)
```

</details>

#### validates DMA cleanup authority on task exit

- validates DMA cleanup authority on task exit
   - Expected: direct_io_cleanup_allowed(buf, release_req(512u64, 44u64, 12u64, false)).is_ok() is true
   - Expected: direct_io_cleanup_allowed(buf, release_req(512u64, 45u64, 12u64, false)).is_err() is true
   - Expected: direct_io_cleanup_allowed(buf, release_req(512u64, 44u64, 12u64, true)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates DMA cleanup authority on task exit")
val buf = dma(512u64, 0x4000u64, 12u64)
expect(direct_io_cleanup_allowed(buf, release_req(512u64, 44u64, 12u64, false)).is_ok()).to_equal(true)
expect(direct_io_cleanup_allowed(buf, release_req(512u64, 45u64, 12u64, false)).is_err()).to_equal(true)
expect(direct_io_cleanup_allowed(buf, release_req(512u64, 44u64, 12u64, true)).is_err()).to_equal(true)
```

</details>

#### benchmark report

#### compares buffered copy and direct DMA on the same fixture

- compares buffered copy and direct DMA on the same fixture
   - Expected: report.fixture_bytes equals `4096u64`
   - Expected: report.backend_tag equals `nvme`
   - Expected: report.buffered_copy_bytes equals `4096u64`
   - Expected: report.direct_dma_copy_bytes equals `0u64`
   - Expected: report.direct_supported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares buffered copy and direct DMA on the same fixture")
val report = direct_io_benchmark_report(make_direct_ext(false), 4096u64, true)
expect(report.fixture_bytes).to_equal(4096u64)
expect(report.backend_tag).to_equal("nvme")
expect(report.buffered_copy_bytes).to_equal(4096u64)
expect(report.direct_dma_copy_bytes).to_equal(0u64)
expect(report.direct_supported).to_equal(true)
```

</details>

#### reports fallback copy cost when direct alignment is not satisfied

- reports fallback copy cost when direct alignment is not satisfied
   - Expected: report.buffered_copy_bytes equals `4096u64`
   - Expected: report.direct_dma_copy_bytes equals `4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports fallback copy cost when direct alignment is not satisfied")
val report = direct_io_benchmark_report(make_direct_ext(false), 4096u64, false)
expect(report.buffered_copy_bytes).to_equal(4096u64)
expect(report.direct_dma_copy_bytes).to_equal(4096u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/driver_dma_direct_io_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-DRIVER-0010 DMA-backed file and block direct I/O.
- FR-DRIVER-0010 DMA-backed file and block direct I/O

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `7c11ba284487a576b9335b3b1742d09019f2d1cc2c4a58372ebc526e5215947f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c11ba284487a576b9335b3b1742d09019f2d1cc2c4a58372ebc526e5215947f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c11ba284487a576b9335b3b1742d09019f2d1cc2c4a58372ebc526e5215947f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/hardware/driver_dma_direct_io_spec.spl
mirror: doc/06_spec/03_system/hardware/driver_dma_direct_io_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/driver_dma_direct_io_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/driver_dma_direct_io_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/driver_dma_direct_io_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'submits aligned reads without buffered copy bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/driver_dma_direct_io_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'submits aligned writes with explicit DMA sync semantics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/driver_dma_direct_io_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unaligned direct I/O when bounce buffering is disabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
