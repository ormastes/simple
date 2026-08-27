# process_sharing_spec

> SOSIX Process Sharing — self-contained unit tests.

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
| Source | `test/unit/os/sosix/process_sharing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SOSIX Process Sharing — self-contained unit tests.

All logic is replicated inline so no OS or syscall imports are required.
Tests cover: process-request constant contracts, dataset/queue constant
contracts, queue-notify syscall ID range, dataset-VFS stub contracts, and
compat-alias integer identities.

## Scenarios

### SOSIX process request state constants

#### REQ_FREE is 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ_FREE is 0
   - Expected: s equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ_FREE is 0")
val s = _PROC_REQ_FREE
expect(s).to_equal(0u8)
```

</details>

#### REQ_PENDING is 1

- REQ_PENDING is 1
   - Expected: s equals `1u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ_PENDING is 1")
val s = _PROC_REQ_PENDING
expect(s).to_equal(1u8)
```

</details>

#### REQ_COMPLETE is 2

- REQ_COMPLETE is 2
   - Expected: s equals `2u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ_COMPLETE is 2")
val s = _PROC_REQ_COMPLETE
expect(s).to_equal(2u8)
```

</details>

#### REQ_ERROR is 3

- REQ_ERROR is 3
   - Expected: s equals `3u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ_ERROR is 3")
val s = _PROC_REQ_ERROR
expect(s).to_equal(3u8)
```

</details>

#### MAX_REQUESTS is 64

- MAX_REQUESTS is 64
   - Expected: n equals `64u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAX_REQUESTS is 64")
val n = _PROC_MAX_REQUESTS
expect(n).to_equal(64u64)
```

</details>

### SOSIX process operation codes

#### OP_NONE is 0

- OP_NONE is 0
   - Expected: _PROC_OP_NONE equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OP_NONE is 0")
expect(_PROC_OP_NONE).to_equal(0u8)
```

</details>

#### OP_FORK is 1

- OP_FORK is 1
   - Expected: _PROC_OP_FORK equals `1u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OP_FORK is 1")
expect(_PROC_OP_FORK).to_equal(1u8)
```

</details>

#### OP_SPAWN is 3

- OP_SPAWN is 3
   - Expected: _PROC_OP_SPAWN equals `3u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OP_SPAWN is 3")
expect(_PROC_OP_SPAWN).to_equal(3u8)
```

</details>

#### OP_EXIT is 5

- OP_EXIT is 5
   - Expected: _PROC_OP_EXIT equals `5u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OP_EXIT is 5")
expect(_PROC_OP_EXIT).to_equal(5u8)
```

</details>

#### OP_SIGNAL is 7

- OP_SIGNAL is 7
   - Expected: _PROC_OP_SIGNAL equals `7u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OP_SIGNAL is 7")
expect(_PROC_OP_SIGNAL).to_equal(7u8)
```

</details>

### SOSIX dataset constants

#### MAX_DATASETS is 64

- MAX_DATASETS is 64
   - Expected: _MAX_DATASETS equals `64u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAX_DATASETS is 64")
expect(_MAX_DATASETS).to_equal(64u64)
```

</details>

#### DATASET_MAX_BYTES is 4096

- DATASET_MAX_BYTES is 4096
   - Expected: _DATASET_MAX_BYTES equals `4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DATASET_MAX_BYTES is 4096")
expect(_DATASET_MAX_BYTES).to_equal(4096u64)
```

</details>

#### NO_DATASET high-bit value is large positive u64

- NO_DATASET high-bit value is large positive u64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NO_DATASET high-bit value is large positive u64")
val high_bit = _NO_DATASET_HIGH_BIT
expect(high_bit).to_be_greater_than(1000000000u64)
```

</details>

### SOSIX queue constants

#### MAX_QUEUES is 32

- MAX_QUEUES is 32
   - Expected: _MAX_QUEUES equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAX_QUEUES is 32")
expect(_MAX_QUEUES).to_equal(32u64)
```

</details>

#### QUEUE_MAX_CAPACITY is 32

- QUEUE_MAX_CAPACITY is 32
   - Expected: _QUEUE_MAX_CAPACITY equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QUEUE_MAX_CAPACITY is 32")
expect(_QUEUE_MAX_CAPACITY).to_equal(32u64)
```

</details>

#### QUEUE_MAX_MSG_BYTES is 128

- QUEUE_MAX_MSG_BYTES is 128
   - Expected: _QUEUE_MAX_MSG_BYTES equals `128u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QUEUE_MAX_MSG_BYTES is 128")
expect(_QUEUE_MAX_MSG_BYTES).to_equal(128u64)
```

</details>

#### POLL_READ bit is 1

- POLL_READ bit is 1
   - Expected: _POLL_READ equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POLL_READ bit is 1")
expect(_POLL_READ).to_equal(1u32)
```

</details>

#### POLL_WRITE bit is 4

- POLL_WRITE bit is 4
   - Expected: _POLL_WRITE equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POLL_WRITE bit is 4")
expect(_POLL_WRITE).to_equal(4u32)
```

</details>

#### POLL_HUP bit is 16

- POLL_HUP bit is 16
   - Expected: _POLL_HUP equals `16u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POLL_HUP bit is 16")
expect(_POLL_HUP).to_equal(16u32)
```

</details>

### SOSIX queue-notify syscall IDs 120-131

#### SYS_DATASET_CREATE is 120

- SYS_DATASET_CREATE is 120
   - Expected: _SYS_DATASET_CREATE equals `120u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_DATASET_CREATE is 120")
expect(_SYS_DATASET_CREATE).to_equal(120u64)
```

</details>

#### SYS_QUEUE_WAIT_SEND is 131

- SYS_QUEUE_WAIT_SEND is 131
   - Expected: _SYS_QUEUE_WAIT_SEND equals `131u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_QUEUE_WAIT_SEND is 131")
expect(_SYS_QUEUE_WAIT_SEND).to_equal(131u64)
```

</details>

#### dataset syscalls are contiguous 120-124

- dataset syscalls are contiguous 120-124
   - Expected: spread equals `4u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dataset syscalls are contiguous 120-124")
val spread = _SYS_DATASET_CLOSE - _SYS_DATASET_CREATE
expect(spread).to_equal(4u64)
```

</details>

#### queue syscalls are contiguous 125-131

- queue syscalls are contiguous 125-131
   - Expected: spread equals `6u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("queue syscalls are contiguous 125-131")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a816ae91e8dabe0171639441ec3246db440f33003d5915adad620b77288fbb32`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a816ae91e8dabe0171639441ec3246db440f33003d5915adad620b77288fbb32`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a816ae91e8dabe0171639441ec3246db440f33003d5915adad620b77288fbb32`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/sosix/process_sharing_spec.spl
mirror: doc/06_spec/unit/os/sosix/process_sharing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/sosix/process_sharing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/sosix/process_sharing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/sosix/process_sharing_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ_FREE is 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/sosix/process_sharing_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ_PENDING is 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/sosix/process_sharing_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ_COMPLETE is 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
