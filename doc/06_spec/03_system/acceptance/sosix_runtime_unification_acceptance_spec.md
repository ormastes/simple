# Sosix Runtime Unification Acceptance Specification

> <details>

<!-- sdn-diagram:id=sosix_runtime_unification_acceptance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sosix_runtime_unification_acceptance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sosix_runtime_unification_acceptance_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sosix_runtime_unification_acceptance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sosix Runtime Unification Acceptance Specification

## Scenarios

### SOSIX runtime unification acceptance

#### admits, completes and releases a positioned read through one ring lifecycle

- Submit a positioned read on a two-slot ring
   - Expected: fs.occupancy() equals `1u64`
- The software provider services it and the pump publishes exactly one completion
   - Expected: fs.pump() equals `1`
- The consumer polls a ready result carrying the transferred count
   - Expected: completion.transferred equals `16u64`
   - Expected: completion.terminal_state equals `SOSIX_OPERATION_COMPLETED`
- Releasing the lease returns the slot to the ring
   - Expected: fs.occupancy() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-AC-2
step("Submit a positioned read on a two-slot ring")
val fs = hosted_fs(2)
val submit = fs.read_at(file_cap(), buffer_ref(), 0u64, 0u64, 16u64, 0u64)
expect(submit.accepted).to_be(true)
expect(fs.occupancy()).to_equal(1u64)
step("The software provider services it and the pump publishes exactly one completion")
expect(fs.service_one(0, 16u64)).to_be(true)
expect(fs.pump()).to_equal(1)
step("The consumer polls a ready result carrying the transferred count")
match fs.poll(submit.operation):
    case TaskPollResult.Ready(result):
        match result:
            case Ok(completion):
                expect(completion.transferred).to_equal(16u64)
                expect(completion.terminal_state).to_equal(SOSIX_OPERATION_COMPLETED)
            case Err(_): fail("a successful read reported an error")
    case TaskPollResult.Pending(_): fail("a completed read was still pending")
step("Releasing the lease returns the slot to the ring")
expect(fs.release(submit.operation).accepted).to_be(true)
expect(fs.occupancy()).to_equal(0u64)
```

</details>

#### rejects an invalid descriptor as a value without ever touching the ring

- Submit with a zero-generation capability, which no lease can name
- The rejection is a typed value: no reservation, no commit, no occupancy
   - Expected: bad.error.kind equals `SOSIX_ERROR_INVALID_CAPABILITY`
   - Expected: fs.occupancy() equals `0u64`
   - Expected: fs.telemetry().reservations equals `0u64`
   - Expected: fs.telemetry().commits equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-AC-5
step("Submit with a zero-generation capability, which no lease can name")
val fs = hosted_fs(1)
val bad = fs.read_at(SosixCapabilityRef(slot: 0, generation: 0), buffer_ref(), 0u64, 0u64, 8u64, 0u64)
step("The rejection is a typed value: no reservation, no commit, no occupancy")
expect(bad.accepted).to_be(false)
expect(bad.error.kind).to_equal(SOSIX_ERROR_INVALID_CAPABILITY)
expect(fs.occupancy()).to_equal(0u64)
expect(fs.telemetry().reservations).to_equal(0u64)
expect(fs.telemetry().commits).to_equal(0u64)
```

</details>

#### waits exactly once for a synchronous read and returns the slot on completion

- Two consecutive synchronous reads share a capacity-one ring
   - Expected: sosix_sync_fs_write_at(fs, driver, file, source, 0u64, 0u64, 10u64, 0u64).outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
- Each call waits once, and the second is admitted because the first released its lease
   - Expected: read.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`
   - Expected: read.waits equals `1u64`
   - Expected: driver.buffer_bytes(sink) equals `acceptance`
   - Expected: fs.occupancy() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-AC-3A
step("Two consecutive synchronous reads share a capacity-one ring")
val fs = hosted_fs(1)
val driver = SosixHostedFileDriver.create()
val path = get_temp_dir() + "/sosix_acceptance_sync.txt"
file_remove(path)
val file = driver.open_path(path)
val source = driver.buffer_from("acceptance")
expect(sosix_sync_fs_write_at(fs, driver, file, source, 0u64, 0u64, 10u64, 0u64).outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
val sink = driver.buffer_from("")
val read = sosix_sync_fs_read_at(fs, driver, file, sink, 0u64, 0u64, 10u64, 0u64)
step("Each call waits once, and the second is admitted because the first released its lease")
expect(read.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(read.waits).to_equal(1u64)
expect(driver.buffer_bytes(sink)).to_equal("acceptance")
expect(fs.occupancy()).to_equal(0u64)
```

</details>

#### carries real host bytes through the ring and reports a missing file as a typed error

- Write through the ring, then read the same bytes back through the ring
   - Expected: sosix_sync_fs_write_at(fs, driver, file, source, 0u64, 0u64, 19u64, 0u64).completion.transferred equals `19u64`
   - Expected: sosix_sync_fs_read_at(fs, driver, file, sink, 8u64, 0u64, 5u64, 0u64).completion.transferred equals `5u64`
   - Expected: driver.buffer_bytes(sink) equals `sosix`
- A path that does not exist surfaces as a native error, not a crash or a silent zero
   - Expected: err.error.kind equals `SOSIX_ERROR_NATIVE`
   - Expected: err.error.native_code equals `SOSIX_FILE_DRIVER_STATUS_IO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-AC-2
step("Write through the ring, then read the same bytes back through the ring")
val fs = hosted_fs(2)
val driver = SosixHostedFileDriver.create()
val path = get_temp_dir() + "/sosix_acceptance_roundtrip.txt"
file_remove(path)
val file = driver.open_path(path)
val source = driver.buffer_from("unified sosix bytes")
expect(sosix_sync_fs_write_at(fs, driver, file, source, 0u64, 0u64, 19u64, 0u64).completion.transferred).to_equal(19u64)
val sink = driver.buffer_from("")
expect(sosix_sync_fs_read_at(fs, driver, file, sink, 8u64, 0u64, 5u64, 0u64).completion.transferred).to_equal(5u64)
expect(driver.buffer_bytes(sink)).to_equal("sosix")
step("A path that does not exist surfaces as a native error, not a crash or a silent zero")
val missing = driver.open_path(get_temp_dir() + "/sosix_acceptance_absent.txt")
file_remove(get_temp_dir() + "/sosix_acceptance_absent.txt")
val err = sosix_sync_fs_read_at(fs, driver, missing, driver.buffer_from(""), 0u64, 0u64, 4u64, 0u64)
expect(err.error.kind).to_equal(SOSIX_ERROR_NATIVE)
expect(err.error.native_code).to_equal(SOSIX_FILE_DRIVER_STATUS_IO)
```

</details>

#### refuses a full queue as a typed value rather than blocking or overwriting

- Fill the only slot, then submit again
   - Expected: second.error.kind equals `SOSIX_ERROR_QUEUE_FULL`
   - Expected: fs.occupancy() equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-AC-5
step("Fill the only slot, then submit again")
val fs = hosted_fs(1)
expect(fs.read_at(file_cap(), buffer_ref(), 0u64, 0u64, 8u64, 0u64).accepted).to_be(true)
val second = fs.read_at(file_cap(), buffer_ref(), 8u64, 0u64, 8u64, 0u64)
expect(second.accepted).to_be(false)
expect(second.error.kind).to_equal(SOSIX_ERROR_QUEUE_FULL)
expect(fs.occupancy()).to_equal(1u64)
```

</details>

#### freezes the host service IDs as one unique table the contracts own alone

- Every frozen ID is known and no two collide
- The contract capsule stays pure: no OS import and no raw runtime extern in any contract file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-AC-1
step("Every frozen ID is known and no two collide")
expect(sosix_service_ids_are_unique()).to_be(true)
expect(sosix_service_ids_all().len()).to_be_greater_than(11)
expect(sosix_service_id_is_known(SOSIX_ID_FS_READ_AT)).to_be(true)
expect(sosix_service_id_is_known(0xDEADu32)).to_be(false)
step("The contract capsule stays pure: no OS import and no raw runtime extern in any contract file")
for name in contract_files():
    val path = "src/lib/common/contracts/sosix/" + name
    expect(file_exists(path)).to_be(true)
    val body = read_file_text(path)
    expect(body).to_not_contain("\nuse os.")
    expect(body).to_not_contain("\nextern fn rt_")
```

</details>

#### leaves no second copy of the lifecycle: the dead Future chain and the unreachable io route are gone

- The four self-referential future modules were deleted, not migrated
- The unreachable SimpleOS io route is gone; its live replacement remains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-AC-4
step("The four self-referential future modules were deleted, not migrated")
expect(file_exists("src/lib/nogc_sync_mut/src/future.spl")).to_be(false)
expect(file_exists("src/lib/nogc_async_mut/src/future.spl")).to_be(false)
expect(file_exists("src/lib/gc_async_mut/src/future.spl")).to_be(false)
expect(file_exists("src/lib/gc_sync_mut/src/future.spl")).to_be(false)
step("The unreachable SimpleOS io route is gone; its live replacement remains")
expect(file_exists("src/os/sosix/io.spl")).to_be(false)
expect(file_exists("src/os/sosix/io_rw.spl")).to_be(true)
```

</details>

#### keeps every row this host cannot prove visible with an owner and a resume command

- The blocked-row record exists and names each row that needs another host, hardware or lane
- Each row carries a resume path, so a later session can pick it up without re-deriving it
- The performance budgets are reported with binary identity rather than left implicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-AC-5
step("The blocked-row record exists and names each row that needs another host, hardware or lane")
expect(file_exists(BLOCKED_ROWS_DOC)).to_be(true)
val doc = read_file_text(BLOCKED_ROWS_DOC)
for row in blocked_rows():
    val key = row.split(" ")[0]
    expect(doc).to_contain(key)
step("Each row carries a resume path, so a later session can pick it up without re-deriving it")
expect(doc).to_contain("Resume command")
expect(doc).to_contain("Missing prerequisite")
step("The performance budgets are reported with binary identity rather than left implicit")
expect(file_exists(PERF_REPORT)).to_be(true)
val perf = read_file_text(PERF_REPORT)
expect(perf).to_contain("Binary identity")
expect(perf).to_contain("ring cycle")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/acceptance/sosix_runtime_unification_acceptance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SOSIX runtime unification acceptance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `da4d70d8ff415ac2e9c2907b9f6f57ec232ffa83332fe0845e664bb8817c78c8`
