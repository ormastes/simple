# Draw Ir Packed Generation Store V3 Specification

> Tests covering packed Draw IR generation storage and bounded handoff.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Packed Generation Store V3 Specification

## Scenarios

### packed Draw IR generation storage and bounded handoff

#### publishes only a completely written sealed generation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes only a completely written sealed generation
   - Expected: store.write(admitted, 11u64) equals `DRAW_IR_PACKED_REASON_OK`
   - Expected: store.write(admitted, 22u64) equals `DRAW_IR_PACKED_REASON_OK`
   - Expected: sealed.content_hash.len() equals `64`
   - Expected: store.publish(sealed) equals `DRAW_IR_PACKED_REASON_OK`
   - Expected: value.generation_ref.generation equals `admitted.generation`
   - Expected: value.content_hash equals `sealed.content_hash`
   - Expected: store.complete(admitted) equals `DRAW_IR_PACKED_REASON_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("publishes only a completely written sealed generation")
var store = DrawIrPackedGenerationStoreV3.bounded(41u64, 2u32, 3u32, 1u32)
var admitted = DrawIrPackedGenerationRefV3(arena_id: 0u64, generation: 0u64, slot: 0u32)
match store.admit(2u32):
    DrawIrPackedAdmissionV3.Admitted(value): admitted = value
    DrawIrPackedAdmissionV3.Refused(reason): expect(false).to_equal(true)
expect(store.write(admitted, 11u64)).to_equal(DRAW_IR_PACKED_REASON_OK)
match store.seal(admitted):
    DrawIrPackedSealV3.Refused(reason): expect(reason).to_equal(DRAW_IR_PACKED_REASON_COUNT_MISMATCH)
    DrawIrPackedSealV3.Sealed(value): expect(false).to_equal(true)
expect(store.write(admitted, 22u64)).to_equal(DRAW_IR_PACKED_REASON_OK)
var sealed = DrawIrPackedSubmissionV3(generation_ref: admitted, row_count: 0u32, content_hash: "")
match store.seal(admitted):
    DrawIrPackedSealV3.Sealed(value): sealed = value
    DrawIrPackedSealV3.Refused(reason): expect(false).to_equal(true)
expect(sealed.content_hash.len()).to_equal(64)
expect(store.publish(sealed)).to_equal(DRAW_IR_PACKED_REASON_OK)
match store.take():
    DrawIrPackedHandoffV3.Ready(value):
        expect(value.generation_ref.generation).to_equal(admitted.generation)
        expect(value.content_hash).to_equal(sealed.content_hash)
    DrawIrPackedHandoffV3.Refused(reason): expect(false).to_equal(true)
expect(store.complete(admitted)).to_equal(DRAW_IR_PACKED_REASON_OK)
```

</details>

#### keeps a sealed generation immutable when the queue is full

- keeps a sealed generation immutable when the queue is full
   - Expected: store.write(first, 7u64) equals `DRAW_IR_PACKED_REASON_OK`
   - Expected: store.publish(first_sealed) equals `DRAW_IR_PACKED_REASON_OK`
   - Expected: store.write(second, 8u64) equals `DRAW_IR_PACKED_REASON_OK`
   - Expected: store.publish(second_sealed) equals `DRAW_IR_PACKED_REASON_QUEUE_FULL`
   - Expected: store.write(second, 9u64) equals `DRAW_IR_PACKED_REASON_STATE`
   - Expected: store.publish(second_sealed) equals `DRAW_IR_PACKED_REASON_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a sealed generation immutable when the queue is full")
var store = DrawIrPackedGenerationStoreV3.bounded(42u64, 2u32, 1u32, 1u32)
var first = DrawIrPackedGenerationRefV3(arena_id: 0u64, generation: 0u64, slot: 0u32)
var second = first
match store.admit(1u32):
    DrawIrPackedAdmissionV3.Admitted(value): first = value
    DrawIrPackedAdmissionV3.Refused(reason): expect(false).to_equal(true)
expect(store.write(first, 7u64)).to_equal(DRAW_IR_PACKED_REASON_OK)
var first_sealed = DrawIrPackedSubmissionV3(generation_ref: first, row_count: 0u32, content_hash: "")
match store.seal(first):
    DrawIrPackedSealV3.Sealed(value): first_sealed = value
    DrawIrPackedSealV3.Refused(reason): expect(false).to_equal(true)
expect(store.publish(first_sealed)).to_equal(DRAW_IR_PACKED_REASON_OK)
match store.admit(1u32):
    DrawIrPackedAdmissionV3.Admitted(value): second = value
    DrawIrPackedAdmissionV3.Refused(reason): expect(false).to_equal(true)
expect(store.write(second, 8u64)).to_equal(DRAW_IR_PACKED_REASON_OK)
var second_sealed = DrawIrPackedSubmissionV3(generation_ref: second, row_count: 0u32, content_hash: "")
match store.seal(second):
    DrawIrPackedSealV3.Sealed(value): second_sealed = value
    DrawIrPackedSealV3.Refused(reason): expect(false).to_equal(true)
expect(store.publish(second_sealed)).to_equal(DRAW_IR_PACKED_REASON_QUEUE_FULL)
expect(store.write(second, 9u64)).to_equal(DRAW_IR_PACKED_REASON_STATE)
match store.take():
    DrawIrPackedHandoffV3.Ready(value): expect(value.generation_ref.generation).to_equal(first.generation)
    DrawIrPackedHandoffV3.Refused(reason): expect(false).to_equal(true)
expect(store.publish(second_sealed)).to_equal(DRAW_IR_PACKED_REASON_OK)
```

</details>

#### rejects overflow, stale references, and slot reuse before completion

- rejects overflow, stale references, and slot reuse before completion
   - Expected: store.write(stale, 1u64) equals `DRAW_IR_PACKED_REASON_STALE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects overflow, stale references, and slot reuse before completion")
var store = DrawIrPackedGenerationStoreV3.bounded(43u64, 1u32, 1u32, 1u32)
match store.admit(2u32):
    DrawIrPackedAdmissionV3.Refused(reason): expect(reason).to_equal(DRAW_IR_PACKED_REASON_CAPACITY)
    DrawIrPackedAdmissionV3.Admitted(value): expect(false).to_equal(true)
var admitted = DrawIrPackedGenerationRefV3(arena_id: 0u64, generation: 0u64, slot: 0u32)
match store.admit(1u32):
    DrawIrPackedAdmissionV3.Admitted(value): admitted = value
    DrawIrPackedAdmissionV3.Refused(reason): expect(false).to_equal(true)
match store.admit(1u32):
    DrawIrPackedAdmissionV3.Refused(reason): expect(reason).to_equal(DRAW_IR_PACKED_REASON_NO_SLOT)
    DrawIrPackedAdmissionV3.Admitted(value): expect(false).to_equal(true)
val stale = DrawIrPackedGenerationRefV3(arena_id: 43u64, generation: admitted.generation + 1u64, slot: admitted.slot)
expect(store.write(stale, 1u64)).to_equal(DRAW_IR_PACKED_REASON_STALE)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering packed Draw IR generation storage and bounded handoff.
- packed Draw IR generation storage and bounded handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6194efc5b136d4c4150a41780813b0099b3997e4ff34ec8b2f766732d9c6fced`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6194efc5b136d4c4150a41780813b0099b3997e4ff34ec8b2f766732d9c6fced`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6194efc5b136d4c4150a41780813b0099b3997e4ff34ec8b2f766732d9c6fced`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.spl
mirror: doc/06_spec/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes only a completely written sealed generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a sealed generation immutable when the queue is full' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overflow, stale references, and slot reuse before completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
