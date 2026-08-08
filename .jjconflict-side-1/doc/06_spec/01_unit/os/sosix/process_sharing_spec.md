# process_sharing_spec

> SOSIX Process Sharing — self-contained unit tests.

<!-- sdn-diagram:id=process_sharing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_sharing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_sharing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_sharing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# process_sharing_spec

SOSIX Process Sharing — self-contained unit tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/process_sharing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SOSIX Process Sharing — self-contained unit tests.

All logic is replicated inline so no OS or syscall imports are required.
Tests cover: process-request constant contracts, dataset/queue constant
contracts, queue-notify syscall ID range, dataset-VFS stub contracts, and
compat-alias integer identities.

## Scenarios

### SOSIX process request state constants

#### REQ_FREE is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _PROC_REQ_FREE
expect(s).to_equal(0u8)
```

</details>

#### REQ_PENDING is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _PROC_REQ_PENDING
expect(s).to_equal(1u8)
```

</details>

#### REQ_COMPLETE is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _PROC_REQ_COMPLETE
expect(s).to_equal(2u8)
```

</details>

#### REQ_ERROR is 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = _PROC_REQ_ERROR
expect(s).to_equal(3u8)
```

</details>

#### MAX_REQUESTS is 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = _PROC_MAX_REQUESTS
expect(n).to_equal(64u64)
```

</details>

### SOSIX process operation codes

#### OP_NONE is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_PROC_OP_NONE).to_equal(0u8)
```

</details>

#### OP_FORK is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_PROC_OP_FORK).to_equal(1u8)
```

</details>

#### OP_SPAWN is 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_PROC_OP_SPAWN).to_equal(3u8)
```

</details>

#### OP_EXIT is 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_PROC_OP_EXIT).to_equal(5u8)
```

</details>

#### OP_SIGNAL is 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_PROC_OP_SIGNAL).to_equal(7u8)
```

</details>

### SOSIX dataset constants

#### MAX_DATASETS is 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_MAX_DATASETS).to_equal(64u64)
```

</details>

#### DATASET_MAX_BYTES is 4096

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_DATASET_MAX_BYTES).to_equal(4096u64)
```

</details>

#### NO_DATASET high-bit value is large positive u64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val high_bit = _NO_DATASET_HIGH_BIT
expect(high_bit).to_be_greater_than(1000000000u64)
```

</details>

### SOSIX queue constants

#### MAX_QUEUES is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_MAX_QUEUES).to_equal(32u64)
```

</details>

#### QUEUE_MAX_CAPACITY is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_QUEUE_MAX_CAPACITY).to_equal(32u64)
```

</details>

#### QUEUE_MAX_MSG_BYTES is 128

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_QUEUE_MAX_MSG_BYTES).to_equal(128u64)
```

</details>

#### POLL_READ bit is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_POLL_READ).to_equal(1u32)
```

</details>

#### POLL_WRITE bit is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_POLL_WRITE).to_equal(4u32)
```

</details>

#### POLL_HUP bit is 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_POLL_HUP).to_equal(16u32)
```

</details>

### SOSIX queue-notify syscall IDs 120-131

#### SYS_DATASET_CREATE is 120

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_SYS_DATASET_CREATE).to_equal(120u64)
```

</details>

#### SYS_QUEUE_WAIT_SEND is 131

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_SYS_QUEUE_WAIT_SEND).to_equal(131u64)
```

</details>

#### dataset syscalls are contiguous 120-124

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spread = _SYS_DATASET_CLOSE - _SYS_DATASET_CREATE
expect(spread).to_equal(4u64)
```

</details>

#### queue syscalls are contiguous 125-131

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spread = _SYS_QUEUE_WAIT_SEND - _SYS_QUEUE_CREATE
expect(spread).to_equal(6u64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
