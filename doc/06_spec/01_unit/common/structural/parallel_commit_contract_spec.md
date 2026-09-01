# Parallel Commit Contract Specification

> Tests covering Parallel parent commit contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parallel Commit Contract Specification

## Scenarios

### Parallel parent commit contract

#### orders results independently of completion order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- orders results independently of completion order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders results independently of completion order")
val first = result_envelope_v1(3, 4, 0, 11, ParallelResultKind.Patch, 71, "b")
val second = result_envelope_v1(3, 8, 0, 12, ParallelResultKind.Patch, 72, "a")
assert_true(result_envelope_v1_well_formed(first))
assert_true(parallel_result_before(first, second, ParallelCommitOrder.TaskIdThenSequence))
assert_true(parallel_result_before(second, first, ParallelCommitOrder.InputKey))
```

</details>

#### rejects overlapping non-reduction updates

- rejects overlapping non-reduction updates


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlapping non-reduction updates")
val left = result_envelope_v1(3, 4, 0, 11, ParallelResultKind.Patch, 71, "a")
val right = result_envelope_v1(3, 8, 0, 11, ParallelResultKind.Append, 72, "b")
assert_true(parallel_results_conflict(left, right))
```

</details>

#### validates a completion-independent deterministic order

- validates a completion-independent deterministic order


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates a completion-independent deterministic order")
val late = result_envelope_v1(3, 9, 0, 13, ParallelResultKind.Patch, 73, "late")
val early = result_envelope_v1(3, 2, 0, 14, ParallelResultKind.Patch, 74, "early")
val validated = parallel_commit_validate([late, early],
    ParallelCommitOrder.TaskIdThenSequence, ParallelConflictPolicy.Reject)
assert_true(validated.ok)
assert_equal(validated.ordered[0].task_id, 2)
```

</details>

#### orders a larger reverse-completion batch without selection-order dependence

- orders a larger reverse-completion batch without selection-order dependence


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders a larger reverse-completion batch without selection-order dependence")
var completion_order = []
var task_id = 16
while task_id > 0:
    completion_order.push(result_envelope_v1(3, task_id, 0,
        100 + task_id, ParallelResultKind.Patch, 200 + task_id,
        "task-{task_id}"))
    task_id = task_id - 1
val ordered = parallel_commit_order_results(completion_order,
    ParallelCommitOrder.TaskIdThenSequence)
assert_equal(ordered.len(), 16)
assert_equal(ordered[0].task_id, 1)
assert_equal(ordered[15].task_id, 16)
```

</details>

#### fails closed when a reduction is mixed with a normal update

- fails closed when a reduction is mixed with a normal update


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when a reduction is mixed with a normal update")
val patch = result_envelope_v1(3, 1, 0, 22, ParallelResultKind.Patch, 75, "patch")
val reduction = result_envelope_v1(3, 2, 0, 22, ParallelResultKind.Reduce, 76, "reduce")
val validated = parallel_commit_validate([patch, reduction],
    ParallelCommitOrder.TaskIdThenSequence, ParallelConflictPolicy.Reduce)
assert_false(validated.ok)
```

</details>

#### requires the reduce policy for overlapping reduction results

- requires the reduce policy for overlapping reduction results


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the reduce policy for overlapping reduction results")
val left = result_envelope_v1(3, 1, 0, 22,
    ParallelResultKind.Reduce, 77, "left")
val right = result_envelope_v1(3, 2, 0, 22,
    ParallelResultKind.Reduce, 78, "right")
val rejected = parallel_commit_validate([left, right],
    ParallelCommitOrder.TaskIdThenSequence, ParallelConflictPolicy.Reject)
val admitted = parallel_commit_validate([left, right],
    ParallelCommitOrder.TaskIdThenSequence, ParallelConflictPolicy.Reduce)
assert_equal(rejected.reason, "reduction-requires-reduce-policy")
assert_true(admitted.ok)
```

</details>

#### publishes child results once in canonical order

- publishes child results once in canonical order


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes child results once in canonical order")
val initial = parallel_commit_state_v1(3, 300)
val late = result_envelope_v1(3, 9, 0, 13, ParallelResultKind.Patch, 73, "late")
val early = result_envelope_v1(3, 2, 0, 14, ParallelResultKind.Patch, 74, "early")
val outcome = parallel_commit_publish_envelopes(initial, [late, early], 301,
    ParallelCommitOrder.TaskIdThenSequence, ParallelConflictPolicy.Reject)
assert_true(outcome.receipt.ok)
assert_true(parallel_commit_receipt_v1_well_formed(outcome.receipt))
assert_equal(outcome.state.revision, 4)
assert_equal(outcome.state.snapshot_token, 301)
assert_equal(outcome.receipt.ordered_task_ids[0], 2)
assert_equal(outcome.receipt.ordered_payload_tokens[1], 73)
```

</details>

#### leaves canonical state unchanged when any input has a stale base

- leaves canonical state unchanged when any input has a stale base


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves canonical state unchanged when any input has a stale base")
val initial = parallel_commit_state_v1(3, 300)
val current = result_envelope_v1(3, 1, 0, 31, ParallelResultKind.Patch, 81, "current")
val stale = result_envelope_v1(2, 2, 0, 32, ParallelResultKind.Patch, 82, "stale")
val outcome = parallel_commit_publish_envelopes(initial, [current, stale], 301,
    ParallelCommitOrder.TaskIdThenSequence, ParallelConflictPolicy.Reject)
assert_false(outcome.receipt.ok)
assert_true(parallel_commit_receipt_v1_well_formed(outcome.receipt))
assert_equal(outcome.receipt.reason, "stale-base-revision")
assert_equal(outcome.state.revision, 3)
assert_equal(outcome.state.snapshot_token, 300)
```

</details>

#### returns a valid diagnostic receipt for malformed owner state

- returns a valid diagnostic receipt for malformed owner state


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a valid diagnostic receipt for malformed owner state")
val invalid = parallel_commit_state_v1(-1, 0)
val outcome = parallel_commit_publish_envelopes(invalid, [], 0,
    ParallelCommitOrder.TaskIdThenSequence, ParallelConflictPolicy.Reject)
assert_false(outcome.receipt.ok)
assert_equal(outcome.receipt.reason, "invalid-owner-state")
assert_true(parallel_commit_receipt_v1_well_formed(outcome.receipt))
```

</details>

#### leaves canonical state unchanged on conflict

- leaves canonical state unchanged on conflict


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves canonical state unchanged on conflict")
val initial = parallel_commit_state_v1(3, 300)
val first = result_envelope_v1(3, 1, 0, 41, ParallelResultKind.Patch, 91, "first")
val second = result_envelope_v1(3, 2, 0, 41, ParallelResultKind.Append, 92, "second")
val outcome = parallel_commit_publish_envelopes(initial, [second, first], 301,
    ParallelCommitOrder.TaskIdThenSequence, ParallelConflictPolicy.Reject)
assert_false(outcome.receipt.ok)
assert_true(parallel_commit_receipt_v1_well_formed(outcome.receipt))
assert_equal(outcome.receipt.reason, "overlapping-write-region")
assert_equal(outcome.state.revision, 3)
assert_equal(outcome.state.snapshot_token, 300)
```

</details>

#### rejects duplicate result identity without publishing

- rejects duplicate result identity without publishing


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects duplicate result identity without publishing")
val initial = parallel_commit_state_v1(3, 300)
val first = result_envelope_v1(3, 1, 0, 51, ParallelResultKind.Patch, 101, "first")
val duplicate = result_envelope_v1(3, 1, 0, 52, ParallelResultKind.Patch, 102, "duplicate")
val rejected = parallel_commit_publish_envelopes(initial, [first, duplicate], 301,
    ParallelCommitOrder.TaskIdThenSequence, ParallelConflictPolicy.Reject)
assert_false(rejected.receipt.ok)
assert_true(parallel_commit_receipt_v1_well_formed(rejected.receipt))
assert_equal(rejected.receipt.reason, "duplicate-result-identity")
assert_equal(rejected.state.revision, 3)
assert_equal(rejected.state.snapshot_token, 300)
```

</details>

#### publishes the same receipt order across completion permutations

- publishes the same receipt order across completion permutations


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes the same receipt order across completion permutations")
val initial = parallel_commit_state_v1(7, 700)
val first = result_envelope_v1(7, 1, 0, 61, ParallelResultKind.NewShard, 111, "c")
val second = result_envelope_v1(7, 2, 0, 62, ParallelResultKind.NewShard, 112, "a")
val third = result_envelope_v1(7, 3, 0, 63, ParallelResultKind.NewShard, 113, "b")
val forward = parallel_commit_publish_envelopes(initial, [first, second, third], 701,
    ParallelCommitOrder.InputKey, ParallelConflictPolicy.Reject)
val reverse = parallel_commit_publish_envelopes(initial, [third, second, first], 701,
    ParallelCommitOrder.InputKey, ParallelConflictPolicy.Reject)
val mixed = parallel_commit_publish_envelopes(initial, [second, first, third], 701,
    ParallelCommitOrder.InputKey, ParallelConflictPolicy.Reject)
assert_equal(forward.receipt.ordered_payload_tokens[0], 112)
assert_equal(reverse.receipt.ordered_payload_tokens[0], 112)
assert_equal(mixed.receipt.ordered_payload_tokens[0], 112)
assert_equal(forward.receipt.ordered_payload_tokens[2], 111)
assert_equal(reverse.receipt.ordered_payload_tokens[2], 111)
assert_equal(mixed.receipt.ordered_payload_tokens[2], 111)
```

</details>

#### rejects malformed receipt element identities

- rejects malformed receipt element identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed receipt element identities")
val invalid_task = parallel_commit_receipt(true, 3, 4, 300, 301,
    1, [0], [0], [74], "")
val invalid_sequence = parallel_commit_receipt(true, 3, 4, 300, 301,
    1, [2], [-1], [74], "")
val invalid_token = parallel_commit_receipt(true, 3, 4, 300, 301,
    1, [2], [0], [0], "")
assert_false(parallel_commit_receipt_v1_well_formed(invalid_task))
assert_false(parallel_commit_receipt_v1_well_formed(invalid_sequence))
assert_false(parallel_commit_receipt_v1_well_formed(invalid_token))
```

</details>

#### pins canonical commit receipt bytes and SHA-256 identity

- pins canonical commit receipt bytes and SHA-256 identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins canonical commit receipt bytes and SHA-256 identity")
val receipt = parallel_commit_receipt(true, 3, 4, 300, 301, 2,
    [2, 9], [0, 0], [74, 73], "")
val encoded = encode_parallel_commit_receipt(receipt)
assert_equal(wire_to_hex(encoded),
    "535043520100000001000000030000000000000004000000000000002c010000000000002d01000000000000020000000000000002000000000000000900000000000000000000000000000000000000000000004a000000000000004900000000000000")
val decoded = decode_parallel_commit_receipt(encoded)
assert_true(decoded.ok)
assert_true(parallel_commit_receipt_v1_equal(receipt, decoded.value))
assert_equal(parallel_commit_receipt_v1_sha256(receipt),
    "6a9ef4e674370f985ac1feebd11a06a405d941fb7e60ad1029fddacca2191456")
```

</details>

#### rejects malformed reserved trailing and invalid receipt wire

- rejects malformed reserved trailing and invalid receipt wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed reserved trailing and invalid receipt wire")
val receipt = parallel_commit_receipt(true, 3, 4, 300, 301, 2,
    [2, 9], [0, 0], [74, 73], "")
var bad_magic = encode_parallel_commit_receipt(receipt)
bad_magic[0] = 0
assert_equal(decode_parallel_commit_receipt(bad_magic).reason,
    "invalid-envelope")
var reserved = encode_parallel_commit_receipt(receipt)
reserved[9] = 1
assert_equal(decode_parallel_commit_receipt(reserved).reason,
    "invalid-reserved")
var trailing = encode_parallel_commit_receipt(receipt)
trailing.push(0)
assert_equal(decode_parallel_commit_receipt(trailing).reason,
    "invalid-wire-length")
var invalid_task = encode_parallel_commit_receipt(receipt)
invalid_task[52] = 0
invalid_task[53] = 0
assert_equal(decode_parallel_commit_receipt(invalid_task).reason,
    "invalid-receipt")
```

</details>

#### round trips one bounded child result payload

- round trips one bounded child result payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round trips one bounded child result payload")
val result = result_envelope_v1(4, 7, 0, 17,
    ParallelResultKind.Patch, 707, "child")
val encoded = encode_result_envelope(result)
assert_equal(wire_to_hex(encoded),
    "5350525301000000040000000000000007000000000000000000000000000000110000000000000001000000c302000000000000050000006368696c64")
val decoded = decode_result_envelope(encoded)
assert_true(decoded.ok)
assert_true(result_envelope_v1_equal(result, decoded.value))
```

</details>

#### rejects malformed child result payload discriminants and reserved bytes

- rejects malformed child result payload discriminants and reserved bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed child result payload discriminants and reserved bytes")
val result = result_envelope_v1(4, 7, 0, 17,
    ParallelResultKind.Patch, 707, "child")
var invalid_kind = encode_result_envelope(result)
invalid_kind[40] = 9
assert_equal(decode_result_envelope(invalid_kind).reason, "invalid-kind")
var reserved = encode_result_envelope(result)
reserved[41] = 1
assert_equal(decode_result_envelope(reserved).reason, "invalid-reserved")
```

</details>

#### round trips a failure receipt with canonical reason evidence

- round trips a failure receipt with canonical reason evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round trips a failure receipt with canonical reason evidence")
val receipt = parallel_commit_receipt(false, 3, 3, 300, 300, 0,
    [], [], [], "stale-base-revision")
val decoded = decode_parallel_commit_receipt(
    encode_parallel_commit_receipt(receipt))
assert_true(decoded.ok)
assert_true(parallel_commit_receipt_v1_equal(receipt, decoded.value))
assert_equal(decoded.value.reason, "stale-base-revision")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/parallel_commit_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Parallel parent commit contract.
- Parallel parent commit contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `03689e2c6e34c416043f0728334156ff2eee804d79da38dac91e9b1f55d44b1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `03689e2c6e34c416043f0728334156ff2eee804d79da38dac91e9b1f55d44b1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `03689e2c6e34c416043f0728334156ff2eee804d79da38dac91e9b1f55d44b1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/parallel_commit_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/parallel_commit_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/parallel_commit_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/parallel_commit_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/parallel_commit_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders results independently of completion order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/parallel_commit_contract_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overlapping non-reduction updates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/parallel_commit_contract_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates a completion-independent deterministic order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
