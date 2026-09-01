# Sosix Process Sharing Specification

> Tests covering sosix_process_sharing feature spec, REQ-SOSIX-SHARE-001 immutable datasets, REQ-SOSIX-SHARE-002 queue transfer, REQ-SOSIX-SHARE-003 dataset attachment.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sosix Process Sharing Specification

## Scenarios

### sosix_process_sharing feature spec

### REQ-SOSIX-SHARE-001 immutable datasets

#### a sealed dataset becomes readable shared data

- a sealed dataset becomes readable shared data
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [1u8, 2u8, 3u8]) equals `3`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_dataset_is_sealed(dataset as u64) is true
   - Expected: sosix_dataset_read_byte(dataset as u64, 2u64) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-SOSIX-SHARE-001
# @req REQ-SOSIX-SHARE-002
# @req REQ-SOSIX-SHARE-003
step("a sealed dataset becomes readable shared data")
sosix_share_init()
val dataset = sosix_dataset_create(3u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [1u8, 2u8, 3u8])).to_equal(3)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_dataset_is_sealed(dataset as u64)).to_equal(true)
expect(sosix_dataset_read_byte(dataset as u64, 2u64)).to_equal(3)
```

</details>

#### writes to a sealed dataset are rejected

- writes to a sealed dataset are rejected
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [4u8, 5u8]) equals `2`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_dataset_write(dataset as u64, 1u64, [6u8]) equals `0 - EINVAL as i64`
   - Expected: sosix_dataset_read_byte(dataset as u64, 1u64) equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes to a sealed dataset are rejected")
sosix_share_init()
val dataset = sosix_dataset_create(2u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [4u8, 5u8])).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(sosix_dataset_write(dataset as u64, 1u64, [6u8])).to_equal(0 - EINVAL as i64)
expect(sosix_dataset_read_byte(dataset as u64, 1u64)).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

### REQ-SOSIX-SHARE-002 queue transfer

#### message payloads traverse a bounded SOSIX queue intact and in order

1. sosix share init
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`
   - Expected: sosix_queue_send(queue as u64, [10u8, 20u8], SOSIX_NO_DATASET) equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `SOSIX_POLL_READ`
   - Expected: recv.status equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: recv.data[0] equals `10u8`
   - Expected: recv.data[1] equals `20u8`
   - Expected: recv.attached_dataset equals `SOSIX_NO_DATASET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(SOSIX_POLL_WRITE)
expect(sosix_queue_send(queue as u64, [10u8, 20u8], SOSIX_NO_DATASET)).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(SOSIX_POLL_READ)

val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(recv.data[0]).to_equal(10u8)
expect(recv.data[1]).to_equal(20u8)
expect(recv.attached_dataset).to_equal(SOSIX_NO_DATASET)
```

</details>

#### should restore write readiness after the queued message is received

1. sosix share init
   - Expected: sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET) equals `1`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `0u32`
   - Expected: sosix_queue_recv(queue as u64).status equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET)).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(0u32)
expect(sosix_queue_recv(queue as u64).status).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(SOSIX_POLL_WRITE)
```

</details>

### REQ-SOSIX-SHARE-003 dataset attachment

#### should transfer a sealed dataset handle with a queue message

1. sosix share init
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [77u8, 88u8]) equals `2`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_queue_send(queue as u64, [9u8], dataset as u64) equals `1`
   - Expected: recv.status equals `1`
   - Expected: recv.attached_dataset equals `dataset as u64`
   - Expected: sosix_dataset_read_byte(recv.attached_dataset, 1u64) equals `88)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(2u64, 0)
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [77u8, 88u8])).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(sosix_queue_send(queue as u64, [9u8], dataset as u64)).to_equal(1)  # oracle: pinned constant asserted by this scenario

val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(recv.attached_dataset).to_equal(dataset as u64)
expect(sosix_dataset_read_byte(recv.attached_dataset, 1u64)).to_equal(88)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should reject unsealed dataset handles as queue attachments

1. sosix share init
   - Expected: sosix_queue_send(queue as u64, [3u8], dataset as u64) equals `0 - EINVAL as i64`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unsealed dataset handles are rejected as queue attachments")
sosix_share_init()
val dataset = sosix_dataset_create(1u64, 0)
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_send(queue as u64, [3u8], dataset as u64)).to_equal(0 - EINVAL as i64)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(0u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/sosix_process_sharing_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sosix_process_sharing feature spec, REQ-SOSIX-SHARE-001 immutable datasets, REQ-SOSIX-SHARE-002 queue transfer, REQ-SOSIX-SHARE-003 dataset attachment.
- sosix_process_sharing feature spec
- REQ-SOSIX-SHARE-001 immutable datasets
- REQ-SOSIX-SHARE-002 queue transfer
- REQ-SOSIX-SHARE-003 dataset attachment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SOSIX-SHARE-001`
- `REQ-SOSIX-SHARE-002`
- `REQ-SOSIX-SHARE-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dea4851be734617f06d7e2ff24505e983bfc824923dc7561d59b04c23bff90c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dea4851be734617f06d7e2ff24505e983bfc824923dc7561d59b04c23bff90c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dea4851be734617f06d7e2ff24505e983bfc824923dc7561d59b04c23bff90c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/03_system/app/os/feature/sosix_process_sharing_spec.spl
mirror: doc/06_spec/03_system/app/os/feature/sosix_process_sharing_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/os/feature/sosix_process_sharing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/os/feature/sosix_process_sharing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a sealed dataset becomes readable shared data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes to a sealed dataset are rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'message payloads traverse a bounded SOSIX queue intact and in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
