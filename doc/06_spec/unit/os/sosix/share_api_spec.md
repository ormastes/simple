# SOSIX Share API Specification

> Purpose: should create an unsealed dataset and seal it for sharing

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX Share API Specification

Purpose: should create an unsealed dataset and seal it for sharing

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/sosix/share_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should create an unsealed dataset and seal it for sharing
Audience: compiler and tooling engineers who maintain this spec

# SOSIX Share API Specification

SOSIX exposes immutable datasets as sealed share handles and bounded queues as
the process-friendly communication primitive. POSIX wrappers can sit above this
surface, but process-sharing behavior is defined here.

## Scenarios

### SOSIX share API immutable dataset lifecycle

#### should create an unsealed dataset and seal it for sharing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should create an unsealed dataset and seal it for sharing
- Verify: should create an unsealed dataset and seal it for sharing
   - Expected: dataset equals `0`
   - Expected: sosix_dataset_is_sealed(dataset as u64) is false
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [7u8, 8u8, 9u8]) equals `3`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_dataset_is_sealed(dataset as u64) is true
   - Expected: sosix_dataset_read_byte(dataset as u64, 1u64) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should create an unsealed dataset and seal it for sharing")
step("Verify: should create an unsealed dataset and seal it for sharing")
# @req: REQ-OS-SharApi-001
sosix_share_init()
val dataset = sosix_dataset_create(3u64, 0)

expect(dataset).to_equal(0)  # oracle: value fixed by the spec contract
expect(sosix_dataset_is_sealed(dataset as u64)).to_equal(false)
expect(sosix_dataset_write(dataset as u64, 0u64, [7u8, 8u8, 9u8])).to_equal(3)  # oracle: value fixed by the spec contract
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)  # oracle: value fixed by the spec contract
expect(sosix_dataset_is_sealed(dataset as u64)).to_equal(true)
expect(sosix_dataset_read_byte(dataset as u64, 1u64)).to_equal(8)  # oracle: value fixed by the spec contract
```

</details>

#### should reject mutation after the dataset is sealed

- should reject mutation after the dataset is sealed
- Verify: should reject mutation after the dataset is sealed
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [1u8, 2u8]) equals `2`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [3u8]) equals `0 - EINVAL as i64`
   - Expected: sosix_dataset_read_byte(dataset as u64, 0u64) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject mutation after the dataset is sealed")
step("Verify: should reject mutation after the dataset is sealed")
# @req: REQ-OS-SharApi-001
sosix_share_init()
val dataset = sosix_dataset_create(2u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [1u8, 2u8])).to_equal(2)  # oracle: value fixed by the spec contract
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)  # oracle: value fixed by the spec contract
expect(sosix_dataset_write(dataset as u64, 0u64, [3u8])).to_equal(0 - EINVAL as i64)
expect(sosix_dataset_read_byte(dataset as u64, 0u64)).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

### SOSIX share API queue dataset attachments

#### should attach a sealed dataset to a queue message

- should attach a sealed dataset to a queue message
- Verify: should attach a sealed dataset to a queue message
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [10u8, 11u8, 12u8, 13u8]) equals `4`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_queue_send(queue as u64, [1u8, 2u8], dataset as u64) equals `2`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `SOSIX_POLL_READ`
   - Expected: recv.status equals `2`
   - Expected: recv.len equals `2u64`
   - Expected: recv.data[0] equals `1u8`
   - Expected: recv.data[1] equals `2u8`
   - Expected: recv.attached_dataset equals `dataset as u64`
   - Expected: sosix_dataset_read_byte(recv.attached_dataset, 3u64) equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should attach a sealed dataset to a queue message")
step("Verify: should attach a sealed dataset to a queue message")
# @req: REQ-OS-SharApi-001
sosix_share_init()
val dataset = sosix_dataset_create(4u64, 0)
val queue = sosix_queue_create(2u64, 8u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [10u8, 11u8, 12u8, 13u8])).to_equal(4)  # oracle: value fixed by the spec contract
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)  # oracle: value fixed by the spec contract
expect(sosix_queue_send(queue as u64, [1u8, 2u8], dataset as u64)).to_equal(2)  # oracle: value fixed by the spec contract
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(SOSIX_POLL_READ)

val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(2)  # oracle: value fixed by the spec contract
expect(recv.len).to_equal(2u64)
expect(recv.data[0]).to_equal(1u8)
expect(recv.data[1]).to_equal(2u8)
expect(recv.attached_dataset).to_equal(dataset as u64)
expect(sosix_dataset_read_byte(recv.attached_dataset, 3u64)).to_equal(13)  # oracle: value fixed by the spec contract
```

</details>

#### should preserve queue write readiness after receiving the attached dataset

- should preserve queue write readiness after receiving the attached dataset
- Verify: should preserve queue write readiness after receiving the attached dataset
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [42u8]) equals `1`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_queue_send(queue as u64, [5u8], dataset as u64) equals `1`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `0u32`
   - Expected: recv.attached_dataset equals `dataset as u64`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should preserve queue write readiness after receiving the attached dataset")
step("Verify: should preserve queue write readiness after receiving the attached dataset")
# @req: REQ-OS-SharApi-001
sosix_share_init()
val dataset = sosix_dataset_create(1u64, 0)
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [42u8])).to_equal(1)  # oracle: value fixed by the spec contract
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)  # oracle: value fixed by the spec contract
expect(sosix_queue_send(queue as u64, [5u8], dataset as u64)).to_equal(1)  # oracle: value fixed by the spec contract
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(0u32)

val recv = sosix_queue_recv(queue as u64)
expect(recv.attached_dataset).to_equal(dataset as u64)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(SOSIX_POLL_WRITE)
```

</details>

#### should reject unsealed dataset attachments

- should reject unsealed dataset attachments
- Verify: should reject unsealed dataset attachments
   - Expected: sosix_queue_send(queue as u64, [9u8], dataset as u64) equals `0 - EINVAL as i64`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject unsealed dataset attachments")
step("Verify: should reject unsealed dataset attachments")
# @req: REQ-OS-SharApi-001
sosix_share_init()
val dataset = sosix_dataset_create(1u64, 0)
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_send(queue as u64, [9u8], dataset as u64)).to_equal(0 - EINVAL as i64)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(0u32)
```

</details>

#### should allow messages without dataset attachments

- should allow messages without dataset attachments
- Verify: should allow messages without dataset attachments
   - Expected: sosix_queue_send(queue as u64, [99u8], SOSIX_NO_DATASET) equals `1`
   - Expected: recv.status equals `1`
   - Expected: recv.attached_dataset equals `SOSIX_NO_DATASET`
   - Expected: recv.data[0] equals `99u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should allow messages without dataset attachments")
step("Verify: should allow messages without dataset attachments")
# @req: REQ-OS-SharApi-001
sosix_share_init()
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_send(queue as u64, [99u8], SOSIX_NO_DATASET)).to_equal(1)  # oracle: value fixed by the spec contract
val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(1)  # oracle: value fixed by the spec contract
expect(recv.attached_dataset).to_equal(SOSIX_NO_DATASET)
expect(recv.data[0]).to_equal(99u8)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-SharApi-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6e21985eac61a0fcd016ad63da1670ced7763615f97236f95f2f3edbffb01442`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6e21985eac61a0fcd016ad63da1670ced7763615f97236f95f2f3edbffb01442`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6e21985eac61a0fcd016ad63da1670ced7763615f97236f95f2f3edbffb01442`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/sosix/share_api_spec.spl
mirror: doc/06_spec/unit/os/sosix/share_api_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/sosix/share_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/sosix/share_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/sosix/share_api_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create an unsealed dataset and seal it for sharing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/os/sosix/share_api_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create an unsealed dataset and seal it for sharing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/sosix/share_api_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject mutation after the dataset is sealed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/os/sosix/share_api_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject mutation after the dataset is sealed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/sosix/share_api_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should attach a sealed dataset to a queue message' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/os/sosix/share_api_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should attach a sealed dataset to a queue message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/sosix/share_api_spec.spl:92:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve queue write readiness after receiving the attached dataset' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/os/sosix/share_api_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsealed dataset attachments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/os/sosix/share_api_spec.spl:122:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should allow messages without dataset attachments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
