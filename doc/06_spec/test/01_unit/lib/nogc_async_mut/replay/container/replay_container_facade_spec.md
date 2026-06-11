# Replay Container Facade Specification

> 1. var proc = ProcessSnapshot create

<!-- sdn-diagram:id=replay_container_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_container_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_container_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_container_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Container Facade Specification

## Scenarios

### nogc_async_mut replay container facades

#### re-exports checkpoint format records

1. var proc = ProcessSnapshot create
2. proc add register
3. proc add page
4. proc add fd
5. var cp = ContainerCheckpoint create
6. cp add process
   - Expected: cp.process_count() equals `1`
   - Expected: cp.total_pages() equals `1`
   - Expected: decoded.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var proc = ProcessSnapshot.create(42)
proc.add_register(7)
proc.add_page(DirtyPage(address: 4096, size: 4096, data_offset: 0))
proc.add_fd(FdEntry(fd: 1, path: "/tmp/out", offset: 0, flags: 0))
var cp = ContainerCheckpoint.create(3, 99)
cp.add_process(proc)
val encoded = encode_checkpoint(cp)
val decoded = decode_checkpoint(encoded)

expect(cp.process_count()).to_equal(1)
expect(cp.total_pages()).to_equal(1)
expect(encoded.len()).to_be_greater_than(0)
expect(decoded.is_ok()).to_equal(true)
```

</details>

#### re-exports container replay driver

1. var driver = ContainerReplayDriver create
2. driver advance event
   - Expected: saved.is_ok() is true
   - Expected: driver.checkpoint_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = ContainerReplayDriver.create("record", "container1")
val saved = driver.save_checkpoint(1)
driver.advance_event()

expect(saved.is_ok()).to_equal(true)
expect(driver.checkpoint_count()).to_equal(1)
expect(driver.info()).to_contain("container1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/replay/container/replay_container_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut replay container facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
