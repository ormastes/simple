# Provider Canonical Json Emitter Specification

> Tests covering SPipe provider atomic canonical JSON emitter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Canonical Json Emitter Specification

## Scenarios

### SPipe provider atomic canonical JSON emitter

#### prevalidates grammar NFC order safe integers and exact predicted size

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-EMIT
```

</details>

#### enforces minus exact plus plan event byte segment output and SHA caps

- enforces minus exact plus plan event byte segment output and SHA caps
   - Expected: provider_response_plan_instruction_count_v1(262143) equals `Ok(262143)`
   - Expected: provider_response_plan_instruction_count_v1(262144) equals `Ok(262144)`
   - Expected: nested_array_plan(15).is_ok() is true
   - Expected: nested_array_plan(16).is_ok() is true
   - Expected: nested_array_plan(17) equals `Err("limit_exceeded")`
   - Expected: null_array_plan(65535).instructions.len() equals `65537`
   - Expected: null_array_plan(65536).instructions.len() equals `65538`
   - Expected: over_member_nested_plan() equals `Err("limit_exceeded")`
   - Expected: result.produced_events equals `pair[1]`
   - Expected: result.produced_bytes equals `pair[1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("enforces minus exact plus plan event byte segment output and SHA caps")
expect(provider_response_plan_instruction_count_v1(262143)).to_equal(Ok(262143))
expect(provider_response_plan_instruction_count_v1(262144)).to_equal(Ok(262144))
expect(provider_response_plan_instruction_count_v1(262145)).to_equal(
    Err("limit_exceeded"))

# Exercise the actual immutable tape at each count, not only the
# scalar guard. The below-cap tapes reach grammar validation; +1 is
# rejected by the instruction ceiling before inspecting element two.
var full_tape: [ProviderJsonEmitInstructionV1] = []
var tape_index = 0
while tape_index < 262145:
    full_tape.push(provider_json_null_v1())
    tape_index = tape_index + 1
expect(provider_response_plan_v1(full_tape, 1048576)).to_equal(
    Err("limit_exceeded"))
full_tape.pop()
expect(provider_response_plan_v1(full_tape, 1048576)).to_equal(
    Err("multiple_json_roots"))
full_tape.pop()
expect(provider_response_plan_v1(full_tape, 1048576)).to_equal(
    Err("multiple_json_roots"))

expect(nested_array_plan(15).is_ok()).to_equal(true)
expect(nested_array_plan(16).is_ok()).to_equal(true)
expect(nested_array_plan(17)).to_equal(Err("limit_exceeded"))
expect(null_array_plan(65535).instructions.len()).to_equal(65537)
expect(null_array_plan(65536).instructions.len()).to_equal(65538)
expect(over_member_nested_plan()).to_equal(Err("limit_exceeded"))

val events_plan = null_array_plan(300)
for pair in [[255, 255], [256, 256], [257, 256]]:
    var event_emitter = fresh_emitter(events_plan, 64,
        emit_budget(), emit_checkpoint())
    val result = event_emitter.step(emit_limits(4096, pair[0])).unwrap()
    expect(result.produced_events).to_equal(pair[1])

val quantum_plan = text_plan(5000)
for pair in [[4095, 4095], [4096, 4096], [4097, 4096]]:
    var byte_emitter = fresh_emitter(quantum_plan, 4096,
        emit_budget(), emit_checkpoint())
    val result = byte_emitter.step(emit_limits(pair[0])).unwrap()
    expect(result.produced_bytes).to_equal(pair[1])

for segment in [4095, 4096]:
    var segment_sha = Sha256StreamV1.begin([]).unwrap()
    var segment_budget = emit_budget()
    var segment_checkpoint = emit_checkpoint()
    expect(ProviderCanonicalJsonEmitterV1.configured(quantum_plan,
        segment, segment_sha, segment_budget,
        segment_checkpoint).is_ok()).to_equal(true)
var excess_sha = Sha256StreamV1.begin([]).unwrap()
var excess_budget = emit_budget()
var excess_checkpoint = emit_checkpoint()
expect(ProviderCanonicalJsonEmitterV1.configured(quantum_plan, 4097,
    excess_sha, excess_budget, excess_checkpoint)).to_equal(
    Err("invalid_sink_limits"))

val two_block_finalize = text_plan(54)
var short_blocks = fresh_emitter(two_block_finalize, 56,
    emit_budget(), emit_checkpoint())
expect(short_blocks.step(emit_limits(4096, 256, 1))).to_equal(
    Err("limit_exceeded"))
for blocks in [2, 3]:
    var enough_blocks = fresh_emitter(two_block_finalize, 56,
        emit_budget(), emit_checkpoint())
    expect(enough_blocks.step(
        emit_limits(4096, 256, blocks)).unwrap().kind).to_equal("ready")
```

</details>

#### typed payload page and explanation builders enforce lower caps

- typed payload page and explanation builders enforce lower caps
   - Expected: provider_response_payload_plan_v1("xxx", 3, 20).is_ok() is true
   - Expected: provider_response_payload_plan_v1("xxx", 4, 20).is_ok() is true
   - Expected: provider_response_page_plan_v1(page, 2, 20).is_ok() is true
   - Expected: provider_response_page_plan_v1(page, 3, 20).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("typed payload page and explanation builders enforce lower caps")
expect(provider_response_payload_plan_v1("xxx", 2, 20)).to_equal(
    Err("limit_exceeded"))
expect(provider_response_payload_plan_v1("xxx", 3, 20).is_ok()).to_equal(true)
expect(provider_response_payload_plan_v1("xxx", 4, 20).is_ok()).to_equal(true)

val page = ["a", "b"]
expect(provider_response_page_plan_v1(page, 1, 20)).to_equal(
    Err("limit_exceeded"))
expect(provider_response_page_plan_v1(page, 2, 20).is_ok()).to_equal(true)
expect(provider_response_page_plan_v1(page, 3, 20).is_ok()).to_equal(true)

val explanation = [
    ProviderResponseTextEntryV1(key: "a", value: "one"),
    ProviderResponseTextEntryV1(key: "b", value: "two")]
expect(provider_response_explanation_plan_v1(
    explanation, 1, 40)).to_equal(Err("limit_exceeded"))
expect(provider_response_explanation_plan_v1(
    explanation, 2, 40).is_ok()).to_equal(true)
expect(provider_response_explanation_plan_v1(
    explanation, 3, 40).is_ok()).to_equal(true)
```

</details>

#### emits identical canonical bytes and hash for one-byte and irregular splits

- emits identical canonical bytes and hash for one-byte and irregular splits
   - Expected: one.0 equals `expected`
   - Expected: irregular.0 equals `expected`
   - Expected: quantum.0 equals `expected`
   - Expected: one.1 equals `sha256_u8_hex(expected)`
   - Expected: irregular.1 equals `one.1`
   - Expected: quantum.1 equals `one.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("emits identical canonical bytes and hash for one-byte and irregular splits")
val expected = "{\"a\":[-9007199254740991,false,null],\"z\":\"\\\"\\\\\\b\\t\\n\\f\\r\\u0000\\u001f café\"}".bytes()
val one = emit_plan(complex_plan(), [1])
val irregular = emit_plan(complex_plan(), [17, 1, 63, 2, 31, 7])
val quantum = emit_plan(complex_plan(), [4096])
expect(one.0).to_equal(expected)
expect(irregular.0).to_equal(expected)
expect(quantum.0).to_equal(expected)
expect(one.1).to_equal(sha256_u8_hex(expected))
expect(irregular.1).to_equal(one.1)
expect(quantum.1).to_equal(one.1)
```

</details>

#### commits full trial cursor and child capabilities atomically

- commits full trial cursor and child capabilities atomically
   - Expected: first.produced_bytes equals `17`
   - Expected: isolated.total_bytes() equals `17`
   - Expected: original.total_bytes() equals `0`
   - Expected: original.cursor.instruction_cursor equals `0`
   - Expected: original.sink.total_bytes() equals `0`
   - Expected: original.sha.total_length equals `0`
   - Expected: source_sha.total_length equals `0`
   - Expected: source_checkpoint.checkpoint_count equals `0`
   - Expected: original_result.produced_bytes equals `17`
   - Expected: original.total_bytes() equals `17`
   - Expected: isolated.total_bytes() equals `17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("commits full trial cursor and child capabilities atomically")
val plan = text_plan(100)
var source_sha = Sha256StreamV1.begin([]).unwrap()
var source_budget = emit_budget()
var source_checkpoint = emit_checkpoint()
var original = ProviderCanonicalJsonEmitterV1.configured(
    plan, 8, source_sha, source_budget, source_checkpoint).unwrap()
var isolated = original
val first = isolated.step(emit_limits(17)).unwrap()
expect(first.produced_bytes).to_equal(17)
expect(isolated.total_bytes()).to_equal(17)
expect(original.total_bytes()).to_equal(0)
expect(original.cursor.instruction_cursor).to_equal(0)
expect(original.sink.total_bytes()).to_equal(0)
expect(original.sha.total_length).to_equal(0)
expect(source_sha.total_length).to_equal(0)
expect(source_budget.consumed(
    provider_budget_category_output_bytes())).to_equal(0)
expect(source_checkpoint.checkpoint_count).to_equal(0)

val original_result = original.step(emit_limits(17)).unwrap()
expect(original_result.produced_bytes).to_equal(17)
expect(original.total_bytes()).to_equal(17)
expect(isolated.total_bytes()).to_equal(17)
```

</details>

#### directly injects sink SHA-update and checkpoint faults at every schedule position

- directly injects sink SHA-update and checkpoint faults at every schedule position
   - Expected: result equals `Err(reason)`
   - Expected: emitter.total_bytes() equals `chunk_index`
   - Expected: emitter.sink.total_bytes() equals `0`
   - Expected: emitter.publishable() is false
   - Expected: emitter.step(emit_limits(1)) equals `Err(reason)`
   - Expected: emitter.take() equals `Err(reason)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("directly injects sink SHA-update and checkpoint faults at every schedule position")
val plan = text_plan(18)
for stage in ["sink", "sha_update", "checkpoint"]:
    val reason = "direct_" + stage + "_fault"
    for chunk_index in [0, 1, 10, 19]:
        var emitter = fault_emitter(plan, stage, chunk_index, reason)
        var result: Result<ProviderWorkStepKindV1, text> = Ok(
            ProviderWorkStepKindV1(kind: "continue",
                produced_bytes: 0, produced_events: 0))
        while result.is_ok() and not emitter.is_ready():
            result = emitter.step(emit_limits(1))
        expect(result).to_equal(Err(reason))
        expect(emitter.total_bytes()).to_equal(chunk_index)
        expect(emitter.sink.total_bytes()).to_equal(0)
        expect(emitter.publishable()).to_equal(false)
        expect(emitter.step(emit_limits(1))).to_equal(Err(reason))
        expect(emitter.take()).to_equal(Err(reason))
```

</details>

#### directly injects SHA-finalize faults at zero first middle and final chunks

- directly injects SHA-finalize faults at zero first middle and final chunks
   - Expected: result equals `Err(reason)`
   - Expected: emitter.sink.total_bytes() equals `0`
   - Expected: emitter.publishable() is false
   - Expected: emitter.step(emit_limits(pair[0])) equals `Err(reason)`
   - Expected: emitter.total_bytes() equals `stable_total`
   - Expected: emitter.take() equals `Err(reason)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("directly injects SHA-finalize faults at zero first middle and final chunks")
val plan = text_plan(18)
for pair in [[20, 0], [10, 1], [2, 9], [1, 19]]:
    val reason = "direct_sha_finalize_fault"
    var emitter = fault_emitter(plan, "sha_finalize", pair[1], reason)
    var result: Result<ProviderWorkStepKindV1, text> = Ok(
        ProviderWorkStepKindV1(kind: "continue",
            produced_bytes: 0, produced_events: 0))
    while result.is_ok() and not emitter.is_ready():
        result = emitter.step(emit_limits(pair[0]))
    expect(result).to_equal(Err(reason))
    expect(emitter.sink.total_bytes()).to_equal(0)
    expect(emitter.publishable()).to_equal(false)
    val stable_total = emitter.total_bytes()
    expect(emitter.step(emit_limits(pair[0]))).to_equal(Err(reason))
    expect(emitter.total_bytes()).to_equal(stable_total)
    expect(emitter.take()).to_equal(Err(reason))
```

</details>

#### fails sink budget at zero first middle and final without cursor commit

- fails sink budget at zero first middle and final without cursor commit
   - Expected: result equals `Err("limit_exceeded")`
   - Expected: emitter.publishable() is false
   - Expected: emitter.sink.total_bytes() equals `0`
   - Expected: emitter.step(emit_limits(1)) equals `Err("limit_exceeded")`
   - Expected: emitter.cursor.instruction_cursor equals `committed_cursor`
   - Expected: emitter.total_bytes() equals `committed_total`
   - Expected: emitter.take() equals `Err("limit_exceeded")`
   - Expected: second_category.cursor.instruction_cursor equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails sink budget at zero first middle and final without cursor commit")
val plan = text_plan(18)
# Byte-zero, immediately-after-first, middle, and final append.
for limit in [0, 1, 10, 19]:
    var emitter = fresh_emitter(plan, 4,
        emit_budget(limit, 100, 100), emit_checkpoint())
    var result: Result<ProviderWorkStepKindV1, text> = Ok(
        ProviderWorkStepKindV1(kind: "continue", produced_bytes: 0,
            produced_events: 0))
    while result.is_ok() and not emitter.is_ready():
        result = emitter.step(emit_limits(1))
    expect(result).to_equal(Err("limit_exceeded"))
    expect(emitter.publishable()).to_equal(false)
    expect(emitter.sink.total_bytes()).to_equal(0)
    val committed_cursor = emitter.cursor.instruction_cursor
    val committed_total = emitter.total_bytes()
    expect(emitter.step(emit_limits(1))).to_equal(Err("limit_exceeded"))
    expect(emitter.cursor.instruction_cursor).to_equal(committed_cursor)
    expect(emitter.total_bytes()).to_equal(committed_total)
    expect(emitter.take()).to_equal(Err("limit_exceeded"))

var second_category = fresh_emitter(plan, 4,
    emit_budget(100, 0, 100), emit_checkpoint())
expect(second_category.step(emit_limits(4))).to_equal(
    Err("limit_exceeded"))
expect(second_category.budget.consumed(
    provider_budget_category_output_bytes())).to_equal(0)
expect(second_category.budget.consumed(
    provider_budget_category_logical_allocations())).to_equal(0)
expect(second_category.cursor.instruction_cursor).to_equal(0)
```

</details>

#### discards first middle final SHA update and finalize failures

- discards first middle final SHA update and finalize failures
   - Expected: result equals `Err("limit_exceeded")`
   - Expected: emitter.publishable() is false
   - Expected: emitter.sink.total_bytes() equals `0`
   - Expected: finalize_result equals `Err("limit_exceeded")`
   - Expected: finalize_after_data.sink.total_bytes() equals `0`
   - Expected: finalize.publishable() is false
   - Expected: finalize.sink.total_bytes() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("discards first middle final SHA update and finalize failures")
val three_blocks = text_plan(190)
for blocks in [0, 1, 2]:
    var emitter = fresh_emitter(three_blocks, 64,
        emit_budget(1000, 1000, blocks), emit_checkpoint())
    var result: Result<ProviderWorkStepKindV1, text> = Ok(
        ProviderWorkStepKindV1(kind: "continue", produced_bytes: 0,
            produced_events: 0))
    while result.is_ok() and not emitter.is_ready():
        result = emitter.step(emit_limits(64))
    expect(result).to_equal(Err("limit_exceeded"))
    expect(emitter.publishable()).to_equal(false)
    expect(emitter.sink.total_bytes()).to_equal(0)

# Three data blocks fit; the separately budgeted finalize block does not.
var finalize_after_data = fresh_emitter(three_blocks, 64,
    emit_budget(1000, 1000, 3), emit_checkpoint())
var finalize_result: Result<ProviderWorkStepKindV1, text> = Ok(
    ProviderWorkStepKindV1(kind: "continue", produced_bytes: 0,
        produced_events: 0))
while finalize_result.is_ok() and not finalize_after_data.is_ready():
    finalize_result = finalize_after_data.step(emit_limits(64))
expect(finalize_result).to_equal(Err("limit_exceeded"))
expect(finalize_after_data.sink.total_bytes()).to_equal(0)

# A 56-byte payload needs two padding blocks: reject first and second.
val two_finalize = text_plan(54)
for blocks in [0, 1]:
    var finalize = fresh_emitter(two_finalize, 56,
        emit_budget(1000, 1000, blocks), emit_checkpoint())
    expect(finalize.step(emit_limits(56, 256, 2))).to_equal(
        Err("limit_exceeded"))
    expect(finalize.publishable()).to_equal(false)
    expect(finalize.sink.total_bytes()).to_equal(0)
```

</details>

#### latches first middle final emission and finalize checkpoints

- latches first middle final emission and finalize checkpoints
   - Expected: result equals `Err("cancelled")`
   - Expected: emitter.publishable() is false
   - Expected: emitter.sink.total_bytes() equals `0`
   - Expected: emitter.step(emit_limits(4)) equals `Err("cancelled")`
   - Expected: emitter.total_bytes() equals `committed_total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("latches first middle final emission and finalize checkpoints")
val plan = text_plan(18)
# Zero, first fan-out, middle, final emission, and finalize checkpoint.
for fail_after in [0, 1, 3, 9, 10]:
    var emitter = fresh_emitter(plan, 4, emit_budget(),
        emit_checkpoint(fail_after, "cancelled"))
    var result: Result<ProviderWorkStepKindV1, text> = Ok(
        ProviderWorkStepKindV1(kind: "continue", produced_bytes: 0,
            produced_events: 0))
    while result.is_ok() and not emitter.is_ready():
        result = emitter.step(emit_limits(4))
    expect(result).to_equal(Err("cancelled"))
    expect(emitter.publishable()).to_equal(false)
    expect(emitter.sink.total_bytes()).to_equal(0)
    val committed_total = emitter.total_bytes()
    expect(emitter.step(emit_limits(4))).to_equal(Err("cancelled"))
    expect(emitter.total_bytes()).to_equal(committed_total)
```

</details>

#### requires exact sink predicted and emitted totals then permits one take

- requires exact sink predicted and emitted totals then permits one take
   - Expected: emitter.take() equals `Err("json_output_not_ready")`
   - Expected: emitter.step(emit_limits(4)).unwrap().kind equals `ready`
   - Expected: emitter.total_bytes() equals `plan.predicted_encoded_bytes`
   - Expected: emitter.sink.total_bytes() equals `plan.predicted_encoded_bytes`
   - Expected: emitter.publishable() is true
   - Expected: emitter.step(emit_limits(4)).unwrap().kind equals `ready`
   - Expected: first.is_ok() is true
   - Expected: first.unwrap().bytes.total_bytes equals `plan.predicted_encoded_bytes`
   - Expected: emitter.take() equals `Err("json_output_taken")`
   - Expected: emitter.step(emit_limits(4)) equals `Err("json_output_taken")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires exact sink predicted and emitted totals then permits one take")
val plan = provider_response_plan_v1([provider_json_null_v1()], 4).unwrap()
var emitter = fresh_emitter(plan, 4, emit_budget(), emit_checkpoint())
expect(emitter.take()).to_equal(Err("json_output_not_ready"))
expect(emitter.step(emit_limits(4)).unwrap().kind).to_equal("ready")
expect(emitter.total_bytes()).to_equal(plan.predicted_encoded_bytes)
expect(emitter.sink.total_bytes()).to_equal(plan.predicted_encoded_bytes)
expect(emitter.publishable()).to_equal(true)
expect(emitter.step(emit_limits(4)).unwrap().kind).to_equal("ready")
val first = emitter.take()
expect(first.is_ok()).to_equal(true)
expect(first.unwrap().bytes.total_bytes).to_equal(plan.predicted_encoded_bytes)
expect(emitter.take()).to_equal(Err("json_output_taken"))
expect(emitter.step(emit_limits(4))).to_equal(Err("json_output_taken"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SPipe provider atomic canonical JSON emitter.
- SPipe provider atomic canonical JSON emitter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-EMIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3535299a32b3aef0d0584dd2c7512e0b6c224d2ff0a92cee5d56071a331a7dcd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3535299a32b3aef0d0584dd2c7512e0b6c224d2ff0a92cee5d56071a331a7dcd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3535299a32b3aef0d0584dd2c7512e0b6c224d2ff0a92cee5d56071a331a7dcd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.spl
mirror: doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.spl:131:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'prevalidates grammar NFC order safe integers and exact predicted size' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enforces minus exact plus plan event byte segment output and SHA caps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.spl:239:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'typed payload page and explanation builders enforce lower caps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.spl:263:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits identical canonical bytes and hash for one-byte and irregular splits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
