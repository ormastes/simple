# Sosix Hosted Fs Perf Specification

> <details>

<!-- sdn-diagram:id=sosix_hosted_fs_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sosix_hosted_fs_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sosix_hosted_fs_perf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sosix_hosted_fs_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sosix Hosted Fs Perf Specification

## Scenarios

### SOSIX hosted capsule perf mechanisms

#### keeps the per-operation ring cycle cost flat from 64 to 512 operations

- Time 64 and 512 full lifecycles on a capacity-1 ring
- Per-op cost at 512 stays within 3x of the cost at 64 (no quadratic term in the lifecycle)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-PERF-FLAT
step("Time 64 and 512 full lifecycles on a capacity-1 ring")
val small = ring_cycle_ns_per_op(64)
val large = ring_cycle_ns_per_op(512)
print("sosix_perf ring_cycle ns/op n=64: " + small.to_string() + " n=512: " + large.to_string())
step("Per-op cost at 512 stays within 3x of the cost at 64 (no quadratic term in the lifecycle)")
expect(large).to_be_less_than(small * 3u64 + 1u64)
```

</details>

#### performs exactly one ring hop per unified read over the file driver

- Prepare a 64-byte file on the host
   - Expected: file_write_text_at(path, 0, "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef") equals `64`
- Time 64 direct positioned reads through the typed alias
- Time 64 reads through the unified ring, sync leg, reference file driver
- Mechanism budget from design §7: one reserve, one commit, one provider take, one completion, one native read per op, and the ring is empty afterwards
   - Expected: fs.telemetry().reservations equals `64u64`
   - Expected: fs.telemetry().commits equals `64u64`
   - Expected: fs.telemetry().provider_takes equals `64u64`
   - Expected: fs.telemetry().completions equals `64u64`
   - Expected: driver.services equals `64u64`
   - Expected: fs.occupancy() equals `0u64`
   - Expected: driver.buffer_bytes(sink) equals `0123456789abcdef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-PERF-HOP
step("Prepare a 64-byte file on the host")
val path = scratch_path()
expect(file_write_text_at(path, 0, "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")).to_equal(64)
step("Time 64 direct positioned reads through the typed alias")
val direct_started = sosix_time_monotonic_now_ns()
var i = 0
while i < 64:
    match file_read_text_at(path, 16, 16):
        case Ok(_): i = i + 1
        case Err(_): fail("direct positioned read failed")
val direct = (sosix_time_monotonic_now_ns() - direct_started) / 64u64
step("Time 64 reads through the unified ring, sync leg, reference file driver")
val fs = setup_sosix_hosted_fs(1)
val driver = SosixHostedFileDriver.create()
val file = driver.open_path(path)
val sink = driver.buffer_from("")
val ring_started = sosix_time_monotonic_now_ns()
var j = 0
while j < 64:
    val result = sosix_sync_fs_read_at(fs, driver, file, sink, 16u64, 0u64, 16u64, 0u64)
    if result.completion.transferred != 16u64:
        fail("unified read did not transfer 16 bytes")
    j = j + 1
val unified = (sosix_time_monotonic_now_ns() - ring_started) / 64u64
print("sosix_perf read16 ns/op direct: " + direct.to_string() + " unified: " + unified.to_string() + " ratio_x100: " + (unified * 100u64 / direct).to_string())
step("Mechanism budget from design §7: one reserve, one commit, one provider take, one completion, one native read per op, and the ring is empty afterwards")
expect(fs.telemetry().reservations).to_equal(64u64)
expect(fs.telemetry().commits).to_equal(64u64)
expect(fs.telemetry().provider_takes).to_equal(64u64)
expect(fs.telemetry().completions).to_equal(64u64)
expect(driver.services).to_equal(64u64)
expect(fs.occupancy()).to_equal(0u64)
expect(driver.buffer_bytes(sink)).to_equal("0123456789abcdef")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/05_perf/lib/sosix_hosted_fs_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SOSIX hosted capsule perf mechanisms

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `d874e820e02c16951ab2d241b18d3a85a9c207ae7a6d6fbe00c9bd5336907d25`
