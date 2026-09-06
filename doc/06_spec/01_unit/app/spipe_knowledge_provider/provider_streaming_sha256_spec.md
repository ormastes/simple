# Provider Streaming Sha256 Specification

> Tests covering SPipe provider incremental SHA-256.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Streaming Sha256 Specification

## Scenarios

### SPipe provider incremental SHA-256

#### matches FIPS vectors and hashes exact raw domain bytes before payload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SHA
```

</details>

#### matches exact documented boundaries under deterministic mixed partitions

- matches exact documented boundaries under deterministic mixed partitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches exact documented boundaries under deterministic mixed partitions")
for size in [0, 1, 55, 56, 63, 64, 65, 4095, 4096, 4097, 1048576]:
    val payload = deterministic_bytes(size)
    val expected = sha256_u8_hex(payload)
    for phase in [0, 3, 7]:
        expect(streamed_partition_digest_from([], payload,
            phase)).to_equal(expected)
```

</details>

#### is invariant at every split point for every length through 65 bytes

- is invariant at every split point for every length through 65 bytes
   - Expected: streamed_digest([], payload, split) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is invariant at every split point for every length through 65 bytes")
var size = 0
while size <= 65:
    val payload = deterministic_bytes(size)
    val expected = sha256_u8_hex(payload)
    var split = 0
    while split <= payload.len():
        expect(streamed_digest([], payload, split)).to_equal(expected)
        split = split + 1
    size = size + 1
```

</details>

#### matches frozen provider domain and payload vectors without self comparison

- matches frozen provider domain and payload vectors without self comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches frozen provider domain and payload vectors without self comparison")
# This is the authoritative lifecycle encoder input used by the signer,
# not a parallel hand-written receipt preimage.
val receipt_unsigned = operation_receipt_unsigned(1, "AUTH-TEST",
    "sha256:" + "0" * 64, "\"cand-1\"", 86400001, 1,
    "ed25519:fe812c12f3ab4ce6ac5db69ac352f906cb1b11ef43fb33e252ef7ff552263889",
    "index_apply", "apply-1", "applied", "sha256:" + "2" * 64,
    "sha256:" + "1" * 64, 1, provider_generation_id(1),
    "sha256:" + "3" * 64, 0, "sha256:" + "1" * 64,
    "spks1-" + "0" * 64, "WS-PROVIDER")
expect(operation_receipt_id(receipt_unsigned)).to_equal(
    "or-036f3ef41c8762b1758b5237415d9594764e226e1883f7a185400e20fa28926b")
expect(digest_domain_input(operation_receipt_domain_bytes(
    receipt_unsigned))).to_equal(
    "036f3ef41c8762b1758b5237415d9594764e226e1883f7a185400e20fa28926b")

expect(provider_candidate_uid("WORK-VECTOR", "SNAP-VECTOR",
    "sha256:" + "3" * 64, "sha256:" + "1" * 64,
    "sha256:" + "2" * 64, "sha256:" + "5" * 64)).to_equal(
    "cand-58514454d831423aabff80e4a016b2e824d94df894ce5bfdcd780d4254d9500a")
val candidate_record = candidate_uid_preimage("WORK-VECTOR",
    "SNAP-VECTOR", "sha256:" + "3" * 64,
    "sha256:" + "1" * 64, "sha256:" + "2" * 64,
    "sha256:" + "5" * 64)
expect(digest_domain_input(candidate_uid_domain_bytes(
    candidate_record))).to_equal(
    "58514454d831423aabff80e4a016b2e824d94df894ce5bfdcd780d4254d9500a")

val payload_text = "{\"base_logical_root\":\"sha256:" + "0" * 64 +
    "\",\"operation_id\":\"apply-1\",\"operations\":[]}"
val payload_value = json_parse_with_error(payload_text).0
expect(provider_payload_preimage(payload_value,
    "index_apply").unwrap()).to_equal(payload_text)
expect(digest_domain_input(provider_payload_domain_bytes(payload_value,
    "index_apply").unwrap())).to_equal(
    "53eac50845e9d3c9014580d3136062cb03e36c7863f947124e63bb674e38308f")
expect(response_hash(payload_text)).to_equal(
    "sha256:6fb8d15fe66a50d9b74605265c77340bf80314e07d81b291976e650b7c1a8639")
expect(streamed_partition_digest([], payload_text.bytes())).to_equal(
    "6fb8d15fe66a50d9b74605265c77340bf80314e07d81b291976e650b7c1a8639")

val replay_input = replay_binding_domain_bytes("WORK-VECTOR",
    "SNAP-VECTOR", "sha256:" + "3" * 64, "index_apply",
    "OP-VECTOR", "sha256:" + "4" * 64, "REQ-VECTOR",
    "sha256:" + "7" * 64, "or-" + "6" * 64)
expect(digest_domain_input(replay_input)).to_equal(
    "59d1b337bcc0603707e82cc41f3cbed9531e652b189fc842810975c52c77582a")
```

</details>

#### handles multiblock partitions and accounts every bounded compression

- handles multiblock partitions and accounts every bounded compression
   - Expected: budget.consumed(provider_budget_category_hash_blocks()) equals `3`
   - Expected: checkpoint.checkpoint_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles multiblock partitions and accounts every bounded compression")
val payload = repeated_byte(257, 90u8)
for split in [1, 63, 64, 127, 128, 193, 256]:
    expect(streamed_digest([], payload, split)).to_equal(
        sha256_u8_hex(payload))

var stream = Sha256StreamV1.begin([]).unwrap()
var budget = sha_budget(3)
var checkpoint = sha_checkpoint()
val two_blocks_and_tail = repeated_byte(130, 113u8)
stream.update(two_blocks_and_tail, 0, 130, budget, checkpoint).unwrap()
expect(stream.finish(budget, checkpoint).unwrap()).to_equal(
    sha256_u8_hex(two_blocks_and_tail))
expect(budget.consumed(provider_budget_category_hash_blocks())).to_equal(3)
expect(checkpoint.checkpoint_count).to_equal(4)
```

</details>

#### checks bounded work at the exact 4 KiB quantum and fails closed

- checks bounded work at the exact 4 KiB quantum and fails closed
   - Expected: checkpoint.checkpoint_count equals `63`
   - Expected: stream.total_length equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("checks bounded work at the exact 4 KiB quantum and fails closed")
val quantum = repeated_byte(8192, 81u8)
var stream = Sha256StreamV1.begin([]).unwrap()
var budget = sha_budget(64)
var checkpoint = sha_checkpoint(63, "deadline_exceeded")
expect(stream.update_bounded(quantum, 0, quantum.len(), budget,
    checkpoint)).to_equal(Err("deadline_exceeded"))
expect(budget.consumed(
    provider_budget_category_hash_blocks())).to_equal(64)
expect(checkpoint.checkpoint_count).to_equal(63)
# Failure is observed at the first 4096-byte work quantum; the second
# half of the large input is never consumed.
expect(stream.total_length).to_equal(4096)
expect(stream.finish(budget,
    checkpoint)).to_equal(Err("sha256_finalized"))
```

</details>

#### rejects invalid ranges before digest mutation and latches the exact reason

- rejects invalid ranges before digest mutation and latches the exact reason
   - Expected: checkpoint.checkpoint_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects invalid ranges before digest mutation and latches the exact reason")
for range in [[-1, 1], [0, -1], [2, 0]]:
    var stream = Sha256StreamV1.begin([]).unwrap()
    var budget = sha_budget()
    var checkpoint = sha_checkpoint()
    expect(stream.update([97u8], range[0], range[1], budget,
        checkpoint)).to_equal(Err("invalid_sha256_range"))
    expect(budget.consumed(
        provider_budget_category_hash_blocks())).to_equal(0)
    expect(checkpoint.checkpoint_count).to_equal(0)
    expect(stream.update([97u8], 0, 1, budget,
        checkpoint)).to_equal(Err("invalid_sha256_range"))
    expect(stream.finish(budget,
        checkpoint)).to_equal(Err("invalid_sha256_range"))
```

</details>

#### fails closed for invalid domains overflow controls and finalization

- fails closed for invalid domains overflow controls and finalization
   - Expected: finished.finish(finish_budget, finish_checkpoint).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for invalid domains overflow controls and finalization")
expect(Sha256StreamV1.begin(repeated_byte(64))).to_equal(
    Err("invalid_hash_domain"))

var overflow = Sha256StreamV1.begin([]).unwrap()
overflow.total_length = 2305843009213693951
var overflow_budget = sha_budget()
var overflow_checkpoint = sha_checkpoint()
expect(overflow.update([1u8], 0, 1, overflow_budget,
    overflow_checkpoint)).to_equal(Err("sha256_length_overflow"))
expect(overflow.finish(overflow_budget,
    overflow_checkpoint)).to_equal(Err("sha256_finalized"))

var limited = Sha256StreamV1.begin([]).unwrap()
var no_blocks = sha_budget(0)
var limited_checkpoint = sha_checkpoint()
expect(limited.update(repeated_byte(64), 0, 64, no_blocks,
    limited_checkpoint)).to_equal(Err("limit_exceeded"))
expect(limited.finish(no_blocks,
    limited_checkpoint)).to_equal(Err("sha256_finalized"))

var cancelled = Sha256StreamV1.begin([]).unwrap()
var cancel_budget = sha_budget()
var cancel_checkpoint = sha_checkpoint(0, "cancelled")
expect(cancelled.update(repeated_byte(64), 0, 64, cancel_budget,
    cancel_checkpoint)).to_equal(Err("cancelled"))
expect(cancelled.finish(cancel_budget,
    cancel_checkpoint)).to_equal(Err("sha256_finalized"))

var finished = Sha256StreamV1.begin([]).unwrap()
var finish_budget = sha_budget()
var finish_checkpoint = sha_checkpoint()
expect(finished.finish(finish_budget, finish_checkpoint).is_ok()).to_equal(true)
expect(finished.finish(finish_budget,
    finish_checkpoint)).to_equal(Err("sha256_finalized"))
expect(finished.update([], 0, 0, finish_budget,
    finish_checkpoint)).to_equal(Err("sha256_finalized"))
```

</details>

#### publishes no digest after finish charge or checkpoint failure

- publishes no digest after finish charge or checkpoint failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("publishes no digest after finish charge or checkpoint failure")
var charge_failed = Sha256StreamV1.begin([]).unwrap()
var no_padding_block = sha_budget(0)
var charge_checkpoint = sha_checkpoint()
expect(charge_failed.finish(no_padding_block,
    charge_checkpoint)).to_equal(Err("limit_exceeded"))
expect(charge_failed.finish(no_padding_block,
    charge_checkpoint)).to_equal(Err("sha256_finalized"))

var checkpoint_failed = Sha256StreamV1.begin([]).unwrap()
var padding_budget = sha_budget()
var stopped = sha_checkpoint(0, "cancelled")
expect(checkpoint_failed.finish(padding_budget,
    stopped)).to_equal(Err("cancelled"))
expect(checkpoint_failed.finish(padding_budget,
    stopped)).to_equal(Err("sha256_finalized"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SPipe provider incremental SHA-256.
- SPipe provider incremental SHA-256

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-SHA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f980e2de536df57d1d1811c1072393963f1df4312292c4f78b7345826e6bbf5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f980e2de536df57d1d1811c1072393963f1df4312292c4f78b7345826e6bbf5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f980e2de536df57d1d1811c1072393963f1df4312292c4f78b7345826e6bbf5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.spl
mirror: doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.spl:102:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'matches FIPS vectors and hashes exact raw domain bytes before payload' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches exact documented boundaries under deterministic mixed partitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is invariant at every split point for every length through 65 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches frozen provider domain and payload vectors without self comparison' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
