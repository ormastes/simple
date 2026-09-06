# Fs Sync Specification

> <details>

<!-- sdn-diagram:id=fs_sync_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fs_sync_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fs_sync_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fs_sync_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fs Sync Specification

## Scenarios

### SOSIX synchronous positioned read

#### waits exactly once for a completion and returns the typed result

- Wait synchronously without spinning
   - Expected: result.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
   - Expected: result.waits equals `1u64`
   - Expected: result.completion.transferred equals `24u64`
- The ring saw one reserve, one commit, one completion
   - Expected: fs.telemetry().reservations equals `1u64`
   - Expected: fs.telemetry().commits equals `1u64`
   - Expected: fs.telemetry().completions equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-FS-SYNC
step("Wait synchronously without spinning")
val fs = setup_sosix_software_ring(2)
val device = ScriptedDevice(status: 0, transferred: 24u64)
val result = sosix_sync_fs_read_at(fs, device, file_cap(), buffer_ref(), 0u64, 0u64, 24u64, 0u64)
expect(result.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(result.waits).to_equal(1u64)
expect(result.completion.transferred).to_equal(24u64)
step("The ring saw one reserve, one commit, one completion")
expect(fs.telemetry().reservations).to_equal(1u64)
expect(fs.telemetry().commits).to_equal(1u64)
expect(fs.telemetry().completions).to_equal(1u64)
```

</details>

#### returns a native failure as a typed error after one wait

- Service the read with a native error
   - Expected: result.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
   - Expected: result.waits equals `1u64`
   - Expected: result.error.kind equals `SOSIX_ERROR_NATIVE`
   - Expected: result.error.native_code equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Service the read with a native error")
val fs = setup_sosix_software_ring(1)
val device = ScriptedDevice(status: -5, transferred: 0u64)
val result = sosix_sync_fs_read_at(fs, device, file_cap(), buffer_ref(), 0u64, 0u64, 8u64, 0u64)
expect(result.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(result.waits).to_equal(1u64)
expect(result.error.kind).to_equal(SOSIX_ERROR_NATIVE)
expect(result.error.native_code).to_equal(-5)
```

</details>

#### reports a native wait timeout without a second wait or a spin

- The device never signals; the native wait times out once
   - Expected: result.outcome equals `SOSIX_SYNC_WAIT_TIMED_OUT`
   - Expected: result.waits equals `1u64`
   - Expected: result.error.kind equals `SOSIX_ERROR_TIMED_OUT`
- The operation is still owned by the ring, not leaked or spun on
   - Expected: fs.occupancy() equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The device never signals; the native wait times out once")
val fs = setup_sosix_software_ring(1)
val result = sosix_sync_fs_read_at(fs, SilentDevice(calls: 0u64), file_cap(), buffer_ref(), 0u64, 0u64, 8u64, 0u64)
expect(result.outcome).to_equal(SOSIX_SYNC_WAIT_TIMED_OUT)
expect(result.waits).to_equal(1u64)
expect(result.error.kind).to_equal(SOSIX_ERROR_TIMED_OUT)
step("The operation is still owned by the ring, not leaked or spun on")
expect(fs.occupancy()).to_equal(1u64)
expect(SOSIX_SYNC_WAIT_BUDGET).to_be_greater_than(1u64)
```

</details>

#### rejects a full queue before any wait

- Reject a stale generation and a full queue
   - Expected: result.outcome equals `SOSIX_SYNC_WAIT_ERROR`
   - Expected: result.waits equals `0u64`
   - Expected: result.error.kind equals `SOSIX_ERROR_QUEUE_FULL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject a stale generation and a full queue")
val fs = setup_sosix_software_ring(1)
val first = fs.read_at(file_cap(), buffer_ref(), 0u64, 0u64, 8u64, 0u64)
expect(first.accepted).to_be(true)
val result = sosix_sync_fs_read_at(fs, ScriptedDevice(status: 0, transferred: 8u64), file_cap(), buffer_ref(), 0u64, 0u64, 8u64, 0u64)
expect(result.outcome).to_equal(SOSIX_SYNC_WAIT_ERROR)
expect(result.waits).to_equal(0u64)
expect(result.error.kind).to_equal(SOSIX_ERROR_QUEUE_FULL)
```

</details>

#### reports a canceled native wait as canceled, not as a timeout

- The native wait is interrupted by cancellation
   - Expected: result.outcome equals `SOSIX_SYNC_WAIT_CANCELED`
   - Expected: result.waits equals `1u64`
   - Expected: result.error.kind equals `SOSIX_ERROR_CANCELED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The native wait is interrupted by cancellation")
val fs = setup_sosix_software_ring(1)
val result = sosix_sync_fs_read_at(fs, CancelingDevice(calls: 0u64), file_cap(), buffer_ref(), 0u64, 0u64, 8u64, 0u64)
expect(result.outcome).to_equal(SOSIX_SYNC_WAIT_CANCELED)
expect(result.waits).to_equal(1u64)
expect(result.error.kind).to_equal(SOSIX_ERROR_CANCELED)
```

</details>

#### returns the ring slot when the synchronous call returns, so a capacity-1 ring serves call after call

- Two consecutive synchronous reads on a capacity-1 ring
   - Expected: first.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
   - Expected: fs.occupancy() equals `0u64`
- The second call is admitted and completes: the first call released its lease on return
   - Expected: second.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
   - Expected: second.completion.transferred equals `8u64`
   - Expected: fs.telemetry().completions equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Two consecutive synchronous reads on a capacity-1 ring")
val fs = setup_sosix_software_ring(1)
val device = ScriptedDevice(status: 0, transferred: 8u64)
val first = sosix_sync_fs_read_at(fs, device, file_cap(), buffer_ref(), 0u64, 0u64, 8u64, 0u64)
expect(first.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(fs.occupancy()).to_equal(0u64)
val second = sosix_sync_fs_read_at(fs, device, file_cap(), buffer_ref(), 8u64, 0u64, 8u64, 0u64)
step("The second call is admitted and completes: the first call released its lease on return")
expect(second.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(second.completion.transferred).to_equal(8u64)
expect(fs.telemetry().completions).to_equal(2u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/sosix/fs_sync_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SOSIX synchronous positioned read

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `fda061f9b2b2b9dbe91cea871cfb3a99bfc7b9035c73856d364f347f63781937`
