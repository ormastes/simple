# SOSIX Sharing Syscall Specification

> Syscalls 120-131 expose immutable datasets and bounded process queues.

<!-- sdn-diagram:id=syscall_sosix_share_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_sosix_share_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_sosix_share_spec -> std
syscall_sosix_share_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_sosix_share_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX Sharing Syscall Specification

Syscalls 120-131 expose immutable datasets and bounded process queues.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/syscall_sosix_share_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Syscalls 120-131 expose immutable datasets and bounded process queues.

## Scenarios

### SOSIX dataset syscalls

#### creates writes seals and maps immutable datasets

1. shared dataset init
   - Expected: handle equals `0`
   - Expected: _dispatch(SyscallArgs(id: 122, arg0: handle as u64, arg1: 0, arg2: &payload as u64, arg3: 4, arg4: 0, arg5: 0)) equals `4`
   - Expected: _dispatch(SyscallArgs(id: 123, arg0: handle as u64, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0)) equals `0`
   - Expected: shared_dataset_read_byte(handle as u64, 2) equals `3`
   - Expected: _dispatch(SyscallArgs(id: 125, arg0: mapped as u64, arg1: 4, arg2: 0, arg3: 0, arg4: 0, arg5: 0)) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()
var payload: [u8] = [1u8, 2u8, 3u8, 4u8]

val handle = _dispatch(SyscallArgs(id: 120, arg0: 4, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0))
expect(handle).to_equal(0)
expect(_dispatch(SyscallArgs(id: 122, arg0: handle as u64, arg1: 0, arg2: &payload as u64, arg3: 4, arg4: 0, arg5: 0))).to_equal(4)
expect(_dispatch(SyscallArgs(id: 123, arg0: handle as u64, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0))).to_equal(0)
expect(shared_dataset_read_byte(handle as u64, 2)).to_equal(3)

val mapped = _dispatch(SyscallArgs(id: 124, arg0: handle as u64, arg1: 0, arg2: 0, arg3: 4, arg4: 0, arg5: 0))
expect(mapped).to_be_greater_than(0)
expect(_dispatch(SyscallArgs(id: 125, arg0: mapped as u64, arg1: 4, arg2: 0, arg3: 0, arg4: 0, arg5: 0))).to_equal(0)
```

</details>

#### rejects invalid file-backed dataset descriptors

1. shared dataset init
2. fd table init
   - Expected: handle equals `-9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()
fd_table_init()

val handle = _dispatch(SyscallArgs(id: 121, arg0: 3, arg1: 0, arg2: 8, arg3: 0, arg4: 0, arg5: 0))
expect(handle).to_equal(-9)
```

</details>

#### rejects write-only file-backed dataset descriptors and preserves offset

1. shared dataset init
2. fd table init
3. fd set
4. fd set offset
   - Expected: handle equals `-9`
   - Expected: fd_get_offset(3) equals `44u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_WRONLY, 30u64)
fd_set_offset(3, 44u64)

val handle = _dispatch(SyscallArgs(id: 121, arg0: 3, arg1: 7, arg2: 8, arg3: 0, arg4: 0, arg5: 0))
expect(handle).to_equal(-9)
expect(fd_get_offset(3)).to_equal(44u64)
```

</details>

#### rejects zero-length file-backed dataset snapshots

1. shared dataset init
2. fd table init
3. fd set
   - Expected: handle equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 30u64)

val handle = _dispatch(SyscallArgs(id: 121, arg0: 3, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0))
expect(handle).to_equal(-22)
```

</details>

#### creates sealed immutable dataset snapshots from file bytes

1. shared dataset init
2. fd table init
3.  clear synthetic fd bytes for test
4. fd set
5. fd set offset
6.  set synthetic fd bytes for test
   - Expected: handle equals `0`
   - Expected: shared_dataset_read_byte(handle as u64, 0) equals `11u8`
   - Expected: shared_dataset_read_byte(handle as u64, 1) equals `12u8`
   - Expected: shared_dataset_read_byte(handle as u64, 2) equals `13u8`
   - Expected: fd_get_offset(3) equals `55u64`
7.  clear synthetic fd bytes for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()
fd_table_init()
_clear_synthetic_fd_bytes_for_test()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 77u64)
fd_set_offset(3, 55u64)
_set_synthetic_fd_bytes_for_test(77u64, [10u8, 11u8, 12u8, 13u8, 14u8])

val handle = _dispatch(SyscallArgs(id: 121, arg0: 3, arg1: 1, arg2: 3, arg3: 0, arg4: 0, arg5: 0))
expect(handle).to_equal(0)
expect(shared_dataset_read_byte(handle as u64, 0)).to_equal(11u8)
expect(shared_dataset_read_byte(handle as u64, 1)).to_equal(12u8)
expect(shared_dataset_read_byte(handle as u64, 2)).to_equal(13u8)
expect(fd_get_offset(3)).to_equal(55u64)

_clear_synthetic_fd_bytes_for_test()
```

</details>

#### rejects out-of-range file-backed dataset snapshots without moving offsets

1. shared dataset init
2. fd table init
3.  clear synthetic fd bytes for test
4. fd set
5. fd set offset
6.  set synthetic fd bytes for test
   - Expected: handle equals `-5`
   - Expected: fd_get_offset(3) equals `66u64`
7.  clear synthetic fd bytes for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()
fd_table_init()
_clear_synthetic_fd_bytes_for_test()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 78u64)
fd_set_offset(3, 66u64)
_set_synthetic_fd_bytes_for_test(78u64, [1u8, 2u8, 3u8])

val handle = _dispatch(SyscallArgs(id: 121, arg0: 3, arg1: 2, arg2: 4, arg3: 0, arg4: 0, arg5: 0))
expect(handle).to_equal(-5)
expect(fd_get_offset(3)).to_equal(66u64)

_clear_synthetic_fd_bytes_for_test()
```

</details>

### SOSIX process queue syscalls

#### creates sends polls and receives queue messages

1. process queue init
2. shared dataset init
   - Expected: shared_dataset_write(dataset as u64, 0, [7u8]) equals `1`
   - Expected: shared_dataset_seal(dataset as u64) equals `0`
   - Expected: queue equals `0`
   - Expected: _dispatch(SyscallArgs(id: 128, arg0: queue as u64, arg1: &payload as u64, arg2: 2, arg3: dataset as u64, arg4: 0, arg5: 0)) equals `2`
   - Expected: _dispatch(SyscallArgs(id: 130, arg0: queue as u64, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0)) & PROCESS_QUEUE_POLL_READ as i64 equals `PROCESS_QUEUE_POLL_READ as i64`
   - Expected: _dispatch(SyscallArgs(id: 129, arg0: queue as u64, arg1: &out as u64, arg2: 2, arg3: &attached as u64, arg4: 0, arg5: 0)) equals `2`
   - Expected: out[0] equals `9u8`
   - Expected: out[1] equals `8u8`
   - Expected: attached equals `dataset as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()
shared_dataset_init()
var payload: [u8] = [9u8, 8u8]
var out: [u8] = [0u8, 0u8]
var attached: u64 = PROCESS_QUEUE_NO_HANDLE
val dataset = shared_dataset_create(1, 0)
expect(shared_dataset_write(dataset as u64, 0, [7u8])).to_equal(1)
expect(shared_dataset_seal(dataset as u64)).to_equal(0)

val queue = _dispatch(SyscallArgs(id: 127, arg0: 2, arg1: 8, arg2: 0, arg3: 0, arg4: 0, arg5: 0))
expect(queue).to_equal(0)
expect(_dispatch(SyscallArgs(id: 128, arg0: queue as u64, arg1: &payload as u64, arg2: 2, arg3: dataset as u64, arg4: 0, arg5: 0))).to_equal(2)
expect(_dispatch(SyscallArgs(id: 130, arg0: queue as u64, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0)) & PROCESS_QUEUE_POLL_READ as i64).to_equal(PROCESS_QUEUE_POLL_READ as i64)

expect(_dispatch(SyscallArgs(id: 129, arg0: queue as u64, arg1: &out as u64, arg2: 2, arg3: &attached as u64, arg4: 0, arg5: 0))).to_equal(2)
expect(out[0]).to_equal(9u8)
expect(out[1]).to_equal(8u8)
expect(attached).to_equal(dataset as u64)
```

</details>

#### rejects invalid dataset attachments

1. process queue init
2. shared dataset init
   - Expected: _dispatch(SyscallArgs(id: 128, arg0: queue as u64, arg1: &payload as u64, arg2: 1, arg3: 65536, arg4: 0, arg5: 0)) equals `-22`
   - Expected: _dispatch(SyscallArgs(id: 128, arg0: queue as u64, arg1: &payload as u64, arg2: 1, arg3: PROCESS_QUEUE_NO_HANDLE, arg4: 0, arg5: 0)) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()
shared_dataset_init()
var payload: [u8] = [1u8]

val queue = _dispatch(SyscallArgs(id: 127, arg0: 1, arg1: 4, arg2: 0, arg3: 0, arg4: 0, arg5: 0))
expect(_dispatch(SyscallArgs(id: 128, arg0: queue as u64, arg1: &payload as u64, arg2: 1, arg3: 65536, arg4: 0, arg5: 0))).to_equal(-22)
expect(_dispatch(SyscallArgs(id: 128, arg0: queue as u64, arg1: &payload as u64, arg2: 1, arg3: PROCESS_QUEUE_NO_HANDLE, arg4: 0, arg5: 0))).to_equal(1)
```

</details>

#### closes queue sides through the ABI

1. process queue init
   - Expected: _dispatch(SyscallArgs(id: 131, arg0: queue as u64, arg1: 1, arg2: 0, arg3: 0, arg4: 0, arg5: 0)) equals `0`
   - Expected: _dispatch(SyscallArgs(id: 129, arg0: queue as u64, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0)) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()

val queue = _dispatch(SyscallArgs(id: 127, arg0: 1, arg1: 4, arg2: 0, arg3: 0, arg4: 0, arg5: 0))
expect(_dispatch(SyscallArgs(id: 131, arg0: queue as u64, arg1: 1, arg2: 0, arg3: 0, arg4: 0, arg5: 0))).to_equal(0)
expect(_dispatch(SyscallArgs(id: 129, arg0: queue as u64, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0))).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
