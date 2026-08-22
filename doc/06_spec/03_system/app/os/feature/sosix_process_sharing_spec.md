# sosix_process_sharing_spec

> Verifies the sosix process sharing behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sosix_process_sharing_spec

Verifies the sosix process sharing behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/sosix_process_sharing_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the sosix process sharing behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### sosix_process_sharing feature spec

### REQ-SOSIX-SHARE-001 immutable datasets

#### should seal a dataset before it becomes readable shared data

- Verify: should seal a dataset before it becomes readable shared data
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [1u8, 2u8, 3u8]) equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_dataset_is_sealed(dataset as u64) is true
   - Expected: sosix_dataset_read_byte(dataset as u64, 2u64) equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SOSIX-SHARE-001 REQ-SOSIX-SHARE-002 REQ-SOSIX-SHARE-003
step("Verify: should seal a dataset before it becomes readable shared data")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
sosix_share_init()
val dataset = sosix_dataset_create(3u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [1u8, 2u8, 3u8])).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(sosix_dataset_is_sealed(dataset as u64)).to_equal(true)
expect(sosix_dataset_read_byte(dataset as u64, 2u64)).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should reject writes after a dataset is sealed

- Verify: should reject writes after a dataset is sealed
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [4u8, 5u8]) equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_dataset_write(dataset as u64, 1u64, [6u8]) equals `0 - EINVAL as i64`
   - Expected: sosix_dataset_read_byte(dataset as u64, 1u64) equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SOSIX-SHARE-001 REQ-SOSIX-SHARE-002 REQ-SOSIX-SHARE-003
step("Verify: should reject writes after a dataset is sealed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
sosix_share_init()
val dataset = sosix_dataset_create(2u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [4u8, 5u8])).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(sosix_dataset_write(dataset as u64, 1u64, [6u8])).to_equal(0 - EINVAL as i64)
expect(sosix_dataset_read_byte(dataset as u64, 1u64)).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

### REQ-SOSIX-SHARE-002 queue transfer

#### should deliver message payloads through a bounded SOSIX queue

- Verify: should deliver message payloads through a bounded SOSIX queue
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`
   - Expected: sosix_queue_send(queue as u64, [10u8, 20u8], SOSIX_NO_DATASET) equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `SOSIX_POLL_READ`
   - Expected: recv.status equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: recv.data[0] equals `10u8`
   - Expected: recv.data[1] equals `20u8`
   - Expected: recv.attached_dataset equals `SOSIX_NO_DATASET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SOSIX-SHARE-001 REQ-SOSIX-SHARE-002 REQ-SOSIX-SHARE-003
step("Verify: should deliver message payloads through a bounded SOSIX queue")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should restore write readiness after the queued message is received
   - Expected: sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET) equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `0u32`
   - Expected: sosix_queue_recv(queue as u64).status equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SOSIX-SHARE-001 REQ-SOSIX-SHARE-002 REQ-SOSIX-SHARE-003
step("Verify: should restore write readiness after the queued message is received")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should transfer a sealed dataset handle with a queue message
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [77u8, 88u8]) equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: sosix_queue_send(queue as u64, [9u8], dataset as u64) equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: recv.status equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: recv.attached_dataset equals `dataset as u64`
   - Expected: sosix_dataset_read_byte(recv.attached_dataset, 1u64) equals `88)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SOSIX-SHARE-001 REQ-SOSIX-SHARE-002 REQ-SOSIX-SHARE-003
step("Verify: should transfer a sealed dataset handle with a queue message")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should reject unsealed dataset handles as queue attachments
   - Expected: sosix_queue_send(queue as u64, [3u8], dataset as u64) equals `0 - EINVAL as i64`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SOSIX-SHARE-001 REQ-SOSIX-SHARE-002 REQ-SOSIX-SHARE-003
step("Verify: should reject unsealed dataset handles as queue attachments")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
sosix_share_init()
val dataset = sosix_dataset_create(1u64, 0)
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_send(queue as u64, [3u8], dataset as u64)).to_equal(0 - EINVAL as i64)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(0u32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `def7c51b1d507a150fedb0fd0712528966e88f60501aee113584ed097843e374`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `def7c51b1d507a150fedb0fd0712528966e88f60501aee113584ed097843e374`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `def7c51b1d507a150fedb0fd0712528966e88f60501aee113584ed097843e374`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/os/feature/sosix_process_sharing_spec.spl
mirror: doc/06_spec/03_system/app/os/feature/sosix_process_sharing_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/os/feature/sosix_process_sharing_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/os/feature/sosix_process_sharing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/os/feature/sosix_process_sharing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should seal a dataset before it becomes readable shared data' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject writes after a dataset is sealed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should deliver message payloads through a bounded SOSIX queue' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should restore write readiness after the queued message is received' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should transfer a sealed dataset handle with a queue message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/os/feature/sosix_process_sharing_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsealed dataset handles as queue attachments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
