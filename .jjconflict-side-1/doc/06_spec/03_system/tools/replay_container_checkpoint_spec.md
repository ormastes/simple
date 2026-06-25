# Replay Container Checkpoint Specification

> <details>

<!-- sdn-diagram:id=replay_container_checkpoint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_container_checkpoint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_container_checkpoint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_container_checkpoint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Container Checkpoint Specification

## Scenarios

### DirtyPage construction

#### stores address, size, data_offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = DirtyPage(address: 4096, size: 4096, data_offset: 0)
expect(page.address).to_equal(4096)
expect(page.size).to_equal(4096)
expect(page.data_offset).to_equal(0)
```

</details>

#### stores large address values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = DirtyPage(address: 1099511627776, size: 4096, data_offset: 8192)
expect(page.address).to_equal(1099511627776)
expect(page.data_offset).to_equal(8192)
```

</details>

### FdEntry construction

#### stores fd, path, offset, flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = FdEntry(fd: 3, path: "/tmp/test.txt", offset: 1024, flags: 2)
expect(entry.fd).to_equal(3)
expect(entry.path).to_equal("/tmp/test.txt")
expect(entry.offset).to_equal(1024)
expect(entry.flags).to_equal(2)
```

</details>

### ProcessSnapshot

#### create sets empty collections

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ProcessSnapshot.create(42)
expect(snap.pid).to_equal(42)
expect(snap.registers.len()).to_equal(0)
expect(snap.memory_pages.len()).to_equal(0)
expect(snap.fd_count).to_equal(0)
```

</details>

#### add_fd increments fd_count

1. var snap = ProcessSnapshot create
2. snap add fd
3. snap add fd
   - Expected: snap.fd_count equals `2`
   - Expected: snap.fd_table.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var snap = ProcessSnapshot.create(10)
snap.add_fd(FdEntry(fd: 0, path: "/dev/stdin", offset: 0, flags: 0))
snap.add_fd(FdEntry(fd: 1, path: "/dev/stdout", offset: 0, flags: 1))
expect(snap.fd_count).to_equal(2)
expect(snap.fd_table.len()).to_equal(2)
```

</details>

### ContainerCheckpoint

#### create sets id and timestamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = ContainerCheckpoint.create(1, 5000)
expect(cp.id).to_equal(1)
expect(cp.timestamp).to_equal(5000)
expect(cp.processes.len()).to_equal(0)
expect(cp.ipc.len()).to_equal(0)
```

</details>

#### process_count returns number of added processes

1. var cp = ContainerCheckpoint create
2. cp add process
3. cp add process
   - Expected: cp.process_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cp = ContainerCheckpoint.create(2, 100)
cp.add_process(ProcessSnapshot.create(10))
cp.add_process(ProcessSnapshot.create(20))
expect(cp.process_count()).to_equal(2)
```

</details>

#### total_pages sums across processes

1. var cp = ContainerCheckpoint create
2. var p1 = ProcessSnapshot create
3. p1 add page
4. p1 add page
5. cp add process
6. var p2 = ProcessSnapshot create
7. p2 add page
8. cp add process
   - Expected: cp.total_pages() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cp = ContainerCheckpoint.create(3, 200)
var p1 = ProcessSnapshot.create(10)
p1.add_page(DirtyPage(address: 4096, size: 4096, data_offset: 0))
p1.add_page(DirtyPage(address: 8192, size: 4096, data_offset: 4096))
cp.add_process(p1)
var p2 = ProcessSnapshot.create(20)
p2.add_page(DirtyPage(address: 16384, size: 4096, data_offset: 8192))
cp.add_process(p2)
expect(cp.total_pages()).to_equal(3)
```

</details>

#### summary contains id and timestamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = ContainerCheckpoint.create(7, 999)
val s = cp.summary()
expect(s).to_contain("id=7")
expect(s).to_contain("ts=999")
```

</details>

### encode_checkpoint / decode_checkpoint round-trip

#### empty checkpoint round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = ContainerCheckpoint.create(1, 100)
val data = encode_checkpoint(cp)
match decode_checkpoint(data):
    case Ok(got):
        expect(got.id).to_equal(1)
        expect(got.timestamp).to_equal(100)
        expect(got.process_count()).to_equal(0)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### checkpoint with process round-trips pid

1. var cp = ContainerCheckpoint create
2. var proc = ProcessSnapshot create
3. proc add register
4. proc add register
5. cp add process
   - Expected: got.processes.len() equals `1`
   - Expected: got.processes[0].pid equals `42`
   - Expected: got.processes[0].registers.len() equals `2`
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cp = ContainerCheckpoint.create(2, 200)
var proc = ProcessSnapshot.create(42)
proc.add_register(100)
proc.add_register(200)
cp.add_process(proc)
val data = encode_checkpoint(cp)
match decode_checkpoint(data):
    case Ok(got):
        expect(got.processes.len()).to_equal(1)
        expect(got.processes[0].pid).to_equal(42)
        expect(got.processes[0].registers.len()).to_equal(2)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### checkpoint with fd_table round-trips entries

1. var cp = ContainerCheckpoint create
2. var proc = ProcessSnapshot create
3. proc add fd
4. cp add process
   - Expected: got.processes[0].fd_table.len() equals `1`
   - Expected: got.processes[0].fd_table[0].fd equals `3`
   - Expected: got.processes[0].fd_table[0].path equals `/tmp/log`
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cp = ContainerCheckpoint.create(5, 500)
var proc = ProcessSnapshot.create(77)
proc.add_fd(FdEntry(fd: 3, path: "/tmp/log", offset: 512, flags: 2))
cp.add_process(proc)
val data = encode_checkpoint(cp)
match decode_checkpoint(data):
    case Ok(got):
        expect(got.processes[0].fd_table.len()).to_equal(1)
        expect(got.processes[0].fd_table[0].fd).to_equal(3)
        expect(got.processes[0].fd_table[0].path).to_equal("/tmp/log")
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### checkpoint with no fd_table round-trips empty

1. var cp = ContainerCheckpoint create
2. var proc = ProcessSnapshot create
3. cp add process
   - Expected: got.processes[0].fd_table.len() equals `0`
   - Expected: got.processes[0].pid equals `10`
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cp = ContainerCheckpoint.create(3, 300)
var proc = ProcessSnapshot.create(10)
cp.add_process(proc)
val data = encode_checkpoint(cp)
match decode_checkpoint(data):
    case Ok(got):
        expect(got.processes[0].fd_table.len()).to_equal(0)
        expect(got.processes[0].pid).to_equal(10)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### checkpoint with dirty page round-trips address

1. var cp = ContainerCheckpoint create
2. var proc = ProcessSnapshot create
3. proc add page
4. cp add process
   - Expected: got.processes[0].memory_pages.len() equals `1`
   - Expected: got.processes[0].memory_pages[0].address equals `65536`
   - Expected: got.processes[0].memory_pages[0].size equals `4096`
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cp = ContainerCheckpoint.create(4, 400)
var proc = ProcessSnapshot.create(99)
proc.add_page(DirtyPage(address: 65536, size: 4096, data_offset: 0))
cp.add_process(proc)
val data = encode_checkpoint(cp)
match decode_checkpoint(data):
    case Ok(got):
        expect(got.processes[0].memory_pages.len()).to_equal(1)
        expect(got.processes[0].memory_pages[0].address).to_equal(65536)
        expect(got.processes[0].memory_pages[0].size).to_equal(4096)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### decode rejects short data

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i32] = [1, 2]
match decode_checkpoint(data):
    case Ok(_):
        expect("should not reach").to_equal("")
    case Err(msg):
        expect(msg).to_contain("too short")
```

</details>

#### decode rejects bad magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i32] = [0, 1, 0, 0, 0, 0, 0]
match decode_checkpoint(data):
    case Ok(_):
        expect("should not reach").to_equal("")
    case Err(msg):
        expect(msg).to_contain("invalid checkpoint magic")
```

</details>

### ContainerReplayDriver.find_checkpoint_before

#### returns None when no checkpoints exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = ContainerReplayDriver.create("record", "ctr-1")
val result = driver.find_checkpoint_before(100)
expect(result.is_none()).to_equal(true)
```

</details>

#### returns the latest checkpoint at or before timestamp

1. var driver = ContainerReplayDriver create
2. driver save checkpoint
3. driver advance event
4. driver advance event
5. driver advance event
6. driver save checkpoint
   - Expected: cp.id equals `1`
   - Expected: "should have found checkpoint" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = ContainerReplayDriver.create("record", "ctr-2")
driver.save_checkpoint(0)
driver.advance_event()
driver.advance_event()
driver.advance_event()
driver.save_checkpoint(1)
val found = driver.find_checkpoint_before(5)
match found:
    case Some(cp):
        expect(cp.id).to_equal(1)
    case None:
        expect("should have found checkpoint").to_equal("")
```

</details>

#### returns None when all checkpoints are after timestamp

1. var driver = ContainerReplayDriver create
2. driver advance event
3. driver advance event
4. driver save checkpoint
   - Expected: found.is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var driver = ContainerReplayDriver.create("record", "ctr-3")
driver.advance_event()
driver.advance_event()
driver.save_checkpoint(0)
val found = driver.find_checkpoint_before(0)
expect(found.is_none()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_container_checkpoint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DirtyPage construction
- FdEntry construction
- ProcessSnapshot
- ContainerCheckpoint
- encode_checkpoint / decode_checkpoint round-trip
- ContainerReplayDriver.find_checkpoint_before

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
