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

#### should seal a dataset before it becomes readable shared data
#### should reject writes after a dataset is sealed

- should reject writes after a dataset is sealed
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [4u8, 5u8]) equals `2`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_dataset_write(dataset as u64, 1u64, [6u8]) equals `0 - EINVAL as i64`
   - Expected: sosix_dataset_read_byte(dataset as u64, 1u64) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject writes after a dataset is sealed")
sosix_share_init()
val dataset = sosix_dataset_create(2u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [4u8, 5u8])).to_equal(2)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_dataset_write(dataset as u64, 1u64, [6u8])).to_equal(0 - EINVAL as i64)
expect(sosix_dataset_read_byte(dataset as u64, 1u64)).to_equal(5)
```

</details>

### REQ-SOSIX-SHARE-002 queue transfer

#### should deliver message payloads through a bounded SOSIX queue

- should deliver message payloads through a bounded SOSIX queue
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`
   - Expected: sosix_queue_send(queue as u64, [10u8, 20u8], SOSIX_NO_DATASET) equals `2`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `SOSIX_POLL_READ`
   - Expected: recv.status equals `2`
   - Expected: recv.data[0] equals `10u8`
   - Expected: recv.data[1] equals `20u8`
   - Expected: recv.attached_dataset equals `SOSIX_NO_DATASET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should deliver message payloads through a bounded SOSIX queue")
sosix_share_init()
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(SOSIX_POLL_WRITE)
expect(sosix_queue_send(queue as u64, [10u8, 20u8], SOSIX_NO_DATASET)).to_equal(2)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(SOSIX_POLL_READ)

val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(2)
expect(recv.data[0]).to_equal(10u8)
expect(recv.data[1]).to_equal(20u8)
expect(recv.attached_dataset).to_equal(SOSIX_NO_DATASET)
```

</details>

#### should restore write readiness after the queued message is received

- should restore write readiness after the queued message is received
   - Expected: sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET) equals `1`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `0u32`
   - Expected: sosix_queue_recv(queue as u64).status equals `1`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should restore write readiness after the queued message is received")
sosix_share_init()
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET)).to_equal(1)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(0u32)
expect(sosix_queue_recv(queue as u64).status).to_equal(1)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(SOSIX_POLL_WRITE)
```

</details>

### REQ-SOSIX-SHARE-003 dataset attachment

#### should transfer a sealed dataset handle with a queue message

- should transfer a sealed dataset handle with a queue message
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [77u8, 88u8]) equals `2`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_queue_send(queue as u64, [9u8], dataset as u64) equals `1`
   - Expected: recv.status equals `1`
   - Expected: recv.attached_dataset equals `dataset as u64`
   - Expected: sosix_dataset_read_byte(recv.attached_dataset, 1u64) equals `88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should transfer a sealed dataset handle with a queue message")
sosix_share_init()
val dataset = sosix_dataset_create(2u64, 0)
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [77u8, 88u8])).to_equal(2)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_queue_send(queue as u64, [9u8], dataset as u64)).to_equal(1)

val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(1)
expect(recv.attached_dataset).to_equal(dataset as u64)
expect(sosix_dataset_read_byte(recv.attached_dataset, 1u64)).to_equal(88)
```

</details>

#### should reject unsealed dataset handles as queue attachments

- should reject unsealed dataset handles as queue attachments
   - Expected: sosix_queue_send(queue as u64, [3u8], dataset as u64) equals `0 - EINVAL as i64`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject unsealed dataset handles as queue attachments")
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
| Source | `test/system/app/os/feature/sosix_process_sharing_spec.spl` |
| Updated | 2026-08-26 |
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

- Canonical SPipe generation for source `6c103d02afe66a16f9687166a9d6fd1b77b67cdd4891b756b8cc2837ddc0c971`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6c103d02afe66a16f9687166a9d6fd1b77b67cdd4891b756b8cc2837ddc0c971`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6c103d02afe66a16f9687166a9d6fd1b77b67cdd4891b756b8cc2837ddc0c971`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/system/app/os/feature/sosix_process_sharing_spec.spl
mirror: doc/06_spec/system/app/os/feature/sosix_process_sharing_spec.md (current)
findings: 14 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/system/app/os/feature/sosix_process_sharing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/os/feature/sosix_process_sharing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/os/feature/sosix_process_sharing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/system/app/os/feature/sosix_process_sharing_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/system/app/os/feature/sosix_process_sharing_spec.spl:31:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should seal a dataset before it becomes readable shared data' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/system/app/os/feature/sosix_process_sharing_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should seal a dataset before it becomes readable shared data' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/os/feature/sosix_process_sharing_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject writes after a dataset is sealed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/os/feature/sosix_process_sharing_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject writes after a dataset is sealed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/os/feature/sosix_process_sharing_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should deliver message payloads through a bounded SOSIX queue' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/os/feature/sosix_process_sharing_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should deliver message payloads through a bounded SOSIX queue' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/os/feature/sosix_process_sharing_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should restore write readiness after the queued message is received' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/os/feature/sosix_process_sharing_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should restore write readiness after the queued message is received' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/os/feature/sosix_process_sharing_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should transfer a sealed dataset handle with a queue message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/os/feature/sosix_process_sharing_spec.spl:102:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsealed dataset handles as queue attachments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
