# Driver Dma Direct Io Specification

> 1. Ok

<!-- sdn-diagram:id=driver_dma_direct_io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_dma_direct_io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_dma_direct_io_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_dma_direct_io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. Ok
   - Expected: result.submitted is true
   - Expected: result.bytes equals `1024u64`
   - Expected: result.backend_tag equals `nvme`
   - Expected: result.status equals `submitted`
   - Expected: result.buffered_copy_bytes equals `0u64`
   - Expected: result.direct_dma_copy_bytes equals `0u64`
   - Expected: result.cleanup_required is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Ok
   - Expected: result.status equals `submitted`
   - Expected: result.bytes equals `512u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = dma(1024u64, 0x2000u64, 9u64)
val req = direct_io_read_request(1u64, 7, buf, 100u32)
expect(direct_io_submit(make_direct_ext(false), req).is_err()).to_equal(true)
```

</details>

#### routes unaligned direct I/O through an explicit bounce result when enabled

1. Ok
   - Expected: result.status equals `bounce-buffered`
   - Expected: result.buffered_copy_bytes equals `1024u64`
   - Expected: result.direct_dma_copy_bytes equals `1024u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = dma(512u64, 0x4000u64, 12u64)
expect(direct_io_cleanup_allowed(buf, release_req(512u64, 44u64, 12u64, false)).is_ok()).to_equal(true)
expect(direct_io_cleanup_allowed(buf, release_req(512u64, 45u64, 12u64, false)).is_err()).to_equal(true)
expect(direct_io_cleanup_allowed(buf, release_req(512u64, 44u64, 12u64, true)).is_err()).to_equal(true)
```

</details>

#### benchmark report

#### compares buffered copy and direct DMA on the same fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = direct_io_benchmark_report(make_direct_ext(false), 4096u64, true)
expect(report.fixture_bytes).to_equal(4096u64)
expect(report.backend_tag).to_equal("nvme")
expect(report.buffered_copy_bytes).to_equal(4096u64)
expect(report.direct_dma_copy_bytes).to_equal(0u64)
expect(report.direct_supported).to_equal(true)
```

</details>

#### reports fallback copy cost when direct alignment is not satisfied

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
