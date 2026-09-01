# Receipt Contract Specification

> Tests covering ExecutionMode wire discriminants, StageFallbackReason vocabulary, VerificationPolicy and VerificationOutcome vocabularies, cpu_selected is distinguishable from gpu_fallback, MappingShardRef exact bytes, StageReceipt exact bytes, VerificationReceipt exact bytes, receipt round trips, receipt decoders hard-reject malformed input, receipt encoders refuse to emit a lying record.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 64 | 64 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Receipt Contract Specification

## Scenarios

### ExecutionMode wire discriminants

#### assigns the three architecture variants to 0..2 in declaration order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- assigns the three architecture variants to 0..2 in declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the three architecture variants to 0..2 in declaration order")
assert_equal(execution_mode_to_u8(ExecutionMode.CpuReference), 0)
assert_equal(execution_mode_to_u8(ExecutionMode.HybridVectorGpu), 1)
assert_equal(execution_mode_to_u8(ExecutionMode.ResidentGpu), 2)
```

</details>

#### declares exactly three modes with 2 as the maximum discriminant

- declares exactly three modes with 2 as the maximum discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares exactly three modes with 2 as the maximum discriminant")
assert_equal(EXECUTION_MODE_COUNT, 3)
assert_equal(EXECUTION_MODE_MAX, 2)
```

</details>

#### round-trips every discriminant through from_u8

- round-trips every discriminant through from_u8


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every discriminant through from_u8")
var i = 0
var mismatches = 0
while i <= EXECUTION_MODE_MAX:
    if execution_mode_to_u8(execution_mode_from_u8(i)) != i:
        mismatches = mismatches + 1
    i = i + 1
assert_equal(mismatches, 0)
```

</details>

#### rejects a discriminant past the end of the frozen enum

- rejects a discriminant past the end of the frozen enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a discriminant past the end of the frozen enum")
assert_true(execution_mode_valid(2))
assert_false(execution_mode_valid(3))
assert_false(execution_mode_valid(-1))
assert_false(execution_mode_valid(255))
```

</details>

#### classifies exactly the two device modes as GPU-using

- classifies exactly the two device modes as GPU-using


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies exactly the two device modes as GPU-using")
assert_false(execution_mode_uses_gpu(ExecutionMode.CpuReference))
assert_true(execution_mode_uses_gpu(ExecutionMode.HybridVectorGpu))
assert_true(execution_mode_uses_gpu(ExecutionMode.ResidentGpu))
```

</details>

#### spells each mode the way the architecture's examples spell it

- spells each mode the way the architecture's examples spell it


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spells each mode the way the architecture's examples spell it")
assert_equal(execution_mode_to_text(ExecutionMode.CpuReference),
             "cpu_reference")
assert_equal(execution_mode_to_text(ExecutionMode.HybridVectorGpu),
             "hybrid_vector_gpu")
assert_equal(execution_mode_to_text(ExecutionMode.ResidentGpu),
             "resident_gpu")
```

</details>

### StageFallbackReason vocabulary

#### carries section 21.4's eight reasons plus None at zero

- carries section 21.4's eight reasons plus None at zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries section 21.4's eight reasons plus None at zero")
assert_equal(STAGE_FALLBACK_REASON_COUNT, 9)
assert_equal(STAGE_FALLBACK_REASON_MAX, 8)
```

</details>

#### assigns discriminants in the order section 21.4 prints them

- assigns discriminants in the order section 21.4 prints them


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns discriminants in the order section 21.4 prints them")
assert_equal(stage_fallback_reason_to_u8(StageFallbackReason.None), 0)
assert_equal(
    stage_fallback_reason_to_u8(StageFallbackReason.UnsupportedFeature),
    1)
assert_equal(
    stage_fallback_reason_to_u8(StageFallbackReason.QueueOverflow), 3)
assert_equal(
    stage_fallback_reason_to_u8(StageFallbackReason.DeviceLost), 6)
assert_equal(
    stage_fallback_reason_to_u8(
        StageFallbackReason.CostModelSelectedCpu),
    8)
```

</details>

#### round-trips every discriminant through from_u8

- round-trips every discriminant through from_u8


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every discriminant through from_u8")
var i = 0
var mismatches = 0
while i <= STAGE_FALLBACK_REASON_MAX:
    if stage_fallback_reason_to_u8(
            stage_fallback_reason_from_u8(i)) != i:
        mismatches = mismatches + 1
    i = i + 1
assert_equal(mismatches, 0)
```

</details>

#### round-trips every discriminant through its text spelling

- round-trips every discriminant through its text spelling


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every discriminant through its text spelling")
var i = 0
var mismatches = 0
while i <= STAGE_FALLBACK_REASON_MAX:
    val s = stage_fallback_reason_to_text(
        stage_fallback_reason_from_u8(i))
    if stage_fallback_reason_from_text(s) != i:
        mismatches = mismatches + 1
    i = i + 1
assert_equal(mismatches, 0)
```

</details>

#### rejects a reason spelling this build does not sanction

- rejects a reason spelling this build does not sanction


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a reason spelling this build does not sanction")
assert_equal(stage_fallback_reason_from_text("glsl_unavailable"), -1)
assert_equal(stage_fallback_reason_from_text("DeviceLost"), -1)
assert_equal(stage_fallback_reason_from_text("device lost"), -1)
```

</details>

#### rejects a discriminant past the end of the frozen enum

- rejects a discriminant past the end of the frozen enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a discriminant past the end of the frozen enum")
assert_true(stage_fallback_reason_valid(8))
assert_false(stage_fallback_reason_valid(9))
assert_false(stage_fallback_reason_valid(-1))
```

</details>

#### classifies cost-model CPU selection as policy and never as forced

- classifies cost-model CPU selection as policy and never as forced


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies cost-model CPU selection as policy and never as forced")
assert_true(
    stage_fallback_is_policy(StageFallbackReason.CostModelSelectedCpu))
assert_false(
    stage_fallback_is_forced(StageFallbackReason.CostModelSelectedCpu))
```

</details>

#### classifies all seven degradations as forced and never as policy

- classifies all seven degradations as forced and never as policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies all seven degradations as forced and never as policy")
var i = 1
var forced = 0
var policy = 0
while i <= 7:
    val r = stage_fallback_reason_from_u8(i)
    if stage_fallback_is_forced(r):
        forced = forced + 1
    if stage_fallback_is_policy(r):
        policy = policy + 1
    i = i + 1
assert_equal(forced, 7)
assert_equal(policy, 0)
```

</details>

#### classifies None as neither policy nor forced

- classifies None as neither policy nor forced


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies None as neither policy nor forced")
assert_false(stage_fallback_is_policy(StageFallbackReason.None))
assert_false(stage_fallback_is_forced(StageFallbackReason.None))
```

</details>

### VerificationPolicy and VerificationOutcome vocabularies

#### freezes five policies and four outcomes

- freezes five policies and four outcomes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("freezes five policies and four outcomes")
assert_equal(VERIFICATION_POLICY_COUNT, 5)
assert_equal(VERIFICATION_POLICY_MAX, 4)
assert_equal(VERIFICATION_OUTCOME_COUNT, 4)
assert_equal(VERIFICATION_OUTCOME_MAX, 3)
```

</details>

#### round-trips every policy and outcome discriminant

- round-trips every policy and outcome discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every policy and outcome discriminant")
var i = 0
var bad = 0
while i <= VERIFICATION_POLICY_MAX:
    if verification_policy_to_u8(verification_policy_from_u8(i)) != i:
        bad = bad + 1
    i = i + 1
var j = 0
while j <= VERIFICATION_OUTCOME_MAX:
    if verification_outcome_to_u8(
            verification_outcome_from_u8(j)) != j:
        bad = bad + 1
    j = j + 1
assert_equal(bad, 0)
```

</details>

#### rejects discriminants past the end of both frozen enums

- rejects discriminants past the end of both frozen enums


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects discriminants past the end of both frozen enums")
assert_false(verification_policy_valid(5))
assert_false(verification_policy_valid(-1))
assert_false(verification_outcome_valid(4))
assert_false(verification_outcome_valid(-1))
```

</details>

#### requires an oracle for OracleCompare only

- requires an oracle for OracleCompare only


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires an oracle for OracleCompare only")
assert_true(
    verification_policy_needs_oracle(VerificationPolicy.OracleCompare))
assert_false(verification_policy_needs_oracle(VerificationPolicy.Full))
assert_false(verification_policy_needs_oracle(VerificationPolicy.Off))
```

</details>

#### treats only Match as clean, never NotRun or OracleUnavailable

- treats only Match as clean, never NotRun or OracleUnavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats only Match as clean, never NotRun or OracleUnavailable")
assert_true(verification_outcome_is_clean(VerificationOutcome.Match))
assert_false(verification_outcome_is_clean(VerificationOutcome.NotRun))
assert_false(
    verification_outcome_is_clean(VerificationOutcome.Mismatch))
assert_false(
    verification_outcome_is_clean(
        VerificationOutcome.OracleUnavailable))
```

</details>

### cpu_selected is distinguishable from gpu_fallback

#### reports a cost-model CPU run as selected and not as a fallback

- reports a cost-model CPU run as selected and not as a fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a cost-model CPU run as selected and not as a fallback")
val r = fixture_stage_receipt("cost_model_selected_cpu")
assert_true(stage_receipt_cpu_selected(r,
                                       ExecutionMode.HybridVectorGpu))
assert_false(stage_receipt_gpu_fallback(r,
                                        ExecutionMode.HybridVectorGpu))
```

</details>

#### reports a device-loss CPU run as a fallback and not as selected

- reports a device-loss CPU run as a fallback and not as selected


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a device-loss CPU run as a fallback and not as selected")
val r = fixture_stage_receipt("device_lost")
assert_false(stage_receipt_cpu_selected(r,
                                        ExecutionMode.HybridVectorGpu))
assert_true(stage_receipt_gpu_fallback(r,
                                       ExecutionMode.HybridVectorGpu))
```

</details>

#### separates all seven forced reasons from the one policy reason

- separates all seven forced reasons from the one policy reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates all seven forced reasons from the one policy reason")
var i = 1
var as_fallback = 0
var as_selected = 0
while i <= 8:
    val r = fixture_stage_receipt(
        stage_fallback_reason_to_text(
            stage_fallback_reason_from_u8(i)))
    if stage_receipt_gpu_fallback(r, ExecutionMode.HybridVectorGpu):
        as_fallback = as_fallback + 1
    if stage_receipt_cpu_selected(r, ExecutionMode.HybridVectorGpu):
        as_selected = as_selected + 1
    i = i + 1
assert_equal(as_fallback, 7)
assert_equal(as_selected, 1)
```

</details>

#### refuses a receipt that changed mode without naming a reason

- refuses a receipt that changed mode without naming a reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a receipt that changed mode without naming a reason")
val r = fixture_stage_receipt("")
assert_false(
    stage_receipt_selection_consistent(r,
                                       ExecutionMode.HybridVectorGpu))
```

</details>

#### refuses a receipt that names a reason without changing mode

- refuses a receipt that names a reason without changing mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a receipt that names a reason without changing mode")
val r = fixture_stage_receipt("device_lost")
assert_false(
    stage_receipt_selection_consistent(r, ExecutionMode.CpuReference))
```

</details>

#### accepts a clean run that neither diverged nor claimed a reason

- accepts a clean run that neither diverged nor claimed a reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a clean run that neither diverged nor claimed a reason")
assert_true(
    stage_receipt_selection_consistent(fixture_clean_receipt(),
                                       ExecutionMode.ResidentGpu))
```

</details>

#### refuses a receipt whose mode text this build cannot name

- refuses a receipt whose mode text this build cannot name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a receipt whose mode text this build cannot name")
var r = fixture_stage_receipt("device_lost")
r.mode = "vulkan_compute"
assert_equal(stage_receipt_mode_u8(r), -1)
assert_false(
    stage_receipt_selection_consistent(r,
                                       ExecutionMode.HybridVectorGpu))
```

</details>

#### refuses a receipt carrying an ad-hoc free-form reason string

- refuses a receipt carrying an ad-hoc free-form reason string


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a receipt carrying an ad-hoc free-form reason string")
val r = fixture_stage_receipt("glsl_unavailable")
assert_equal(stage_receipt_fallback_reason(r), -1)
assert_false(
    stage_receipt_selection_consistent(r,
                                       ExecutionMode.HybridVectorGpu))
```

</details>

#### refuses to serialize a silent fallback at all

- refuses to serialize a silent fallback at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to serialize a silent fallback at all")
val r = fixture_stage_receipt("")
assert_false(stage_receipt_encodable(r, ExecutionMode.HybridVectorGpu))
assert_equal(
    encode_stage_receipt(r, ExecutionMode.HybridVectorGpu).len(), 0)
```

</details>

### MappingShardRef exact bytes

#### encodes the absent handle to the hand-derived golden vector

- encodes the absent handle to the hand-derived golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the absent handle to the hand-derived golden vector")
assert_equal(wire_to_hex(encode_mapping_shard_ref(
                 mapping_shard_ref_none())),
             GOLDEN_SHARD_REF_NONE)
```

</details>

#### encodes a populated handle to the hand-derived golden vector

- encodes a populated handle to the hand-derived golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a populated handle to the hand-derived golden vector")
assert_equal(wire_to_hex(encode_mapping_shard_ref(
                 fixture_shard_ref())),
             GOLDEN_SHARD_REF_BASIC)
```

</details>

#### encodes to exactly the frozen 52-byte body plus an 8-byte envelope

- encodes to exactly the frozen 52-byte body plus an 8-byte envelope


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes to exactly the frozen 52-byte body plus an 8-byte envelope")
assert_equal(MAPPING_SHARD_REF_LEN, 52)
assert_equal(encode_mapping_shard_ref(fixture_shard_ref()).len(), 60)
```

</details>

### StageReceipt exact bytes

#### encodes a cost-model CPU selection to the golden vector

- encodes a cost-model CPU selection to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a cost-model CPU selection to the golden vector")
assert_equal(
    wire_to_hex(encode_stage_receipt(
        fixture_stage_receipt("cost_model_selected_cpu"),
        ExecutionMode.HybridVectorGpu)),
    GOLDEN_STAGE_RECEIPT_CPU_SELECTED)
```

</details>

#### encodes a forced device-loss fallback to the golden vector

- encodes a forced device-loss fallback to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a forced device-loss fallback to the golden vector")
assert_equal(
    wire_to_hex(encode_stage_receipt(
        fixture_stage_receipt("device_lost"),
        ExecutionMode.HybridVectorGpu)),
    GOLDEN_STAGE_RECEIPT_GPU_FALLBACK)
```

</details>

#### encodes a clean resident-GPU run to the golden vector

- encodes a clean resident-GPU run to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a clean resident-GPU run to the golden vector")
assert_equal(
    wire_to_hex(encode_stage_receipt(fixture_clean_receipt(),
                                     ExecutionMode.ResidentGpu)),
    GOLDEN_STAGE_RECEIPT_CLEAN)
```

</details>

#### differs between the two cases in exactly one byte

- differs between the two cases in exactly one byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("differs between the two cases in exactly one byte")
val a = encode_stage_receipt(
    fixture_stage_receipt("cost_model_selected_cpu"),
    ExecutionMode.HybridVectorGpu)
val b = encode_stage_receipt(fixture_stage_receipt("device_lost"),
                             ExecutionMode.HybridVectorGpu)
assert_equal(a.len(), b.len())
var i = 0
var diffs = 0
var at = -1
while i < a.len():
    if a[i] != b[i]:
        diffs = diffs + 1
        at = i
    i = i + 1
assert_equal(diffs, 1)
# Byte 8 (envelope) + 4 (contract_version) + 1 (requested) + 1 (mode)
# = offset 14, the fallback_reason slot.
assert_equal(at, 14)
```

</details>

#### uses the frozen 63-byte fixed head

- uses the frozen 63-byte fixed head


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the frozen 63-byte fixed head")
assert_equal(STAGE_RECEIPT_HEAD_LEN, 63)
```

</details>

### VerificationReceipt exact bytes

#### encodes an oracle mismatch to the hand-derived golden vector

- encodes an oracle mismatch to the hand-derived golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes an oracle mismatch to the hand-derived golden vector")
assert_equal(
    wire_to_hex(encode_verification_receipt(
        fixture_verification_mismatch())),
    GOLDEN_VERIFICATION_MISMATCH)
```

</details>

#### encodes a never-run verification to the hand-derived golden vector

- encodes a never-run verification to the hand-derived golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a never-run verification to the hand-derived golden vector")
assert_equal(
    wire_to_hex(encode_verification_receipt(
        verification_receipt_not_run("", "",
                                     ExecutionMode.CpuReference))),
    GOLDEN_VERIFICATION_NOT_RUN)
```

</details>

#### uses the frozen 91-byte fixed head

- uses the frozen 91-byte fixed head


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the frozen 91-byte fixed head")
assert_equal(VERIFICATION_RECEIPT_HEAD_LEN, 91)
```

</details>

### receipt round trips

#### round-trips a populated MappingShardRef

- round-trips a populated MappingShardRef


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a populated MappingShardRef")
val d = decode_mapping_shard_ref(
    encode_mapping_shard_ref(fixture_shard_ref()))
assert_true(d.ok)
assert_true(mapping_shard_ref_equal(d.value, fixture_shard_ref()))
```

</details>

#### round-trips the absent MappingShardRef and keeps it recognisable

- round-trips the absent MappingShardRef and keeps it recognisable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips the absent MappingShardRef and keeps it recognisable")
val d = decode_mapping_shard_ref(
    encode_mapping_shard_ref(mapping_shard_ref_none()))
assert_true(d.ok)
assert_true(mapping_shard_ref_is_none(d.value))
assert_false(mapping_shard_ref_is_none(fixture_shard_ref()))
```

</details>

#### round-trips a stage receipt and preserves the requested mode

- round-trips a stage receipt and preserves the requested mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a stage receipt and preserves the requested mode")
val r = fixture_stage_receipt("cost_model_selected_cpu")
val d = decode_stage_receipt(
    encode_stage_receipt(r, ExecutionMode.HybridVectorGpu))
assert_true(d.ok)
assert_true(stage_receipt_wire_equal(d.value, r))
assert_equal(execution_mode_to_u8(d.requested), 1)
```

</details>

#### round-trips every fallback reason without collapsing any two

- round-trips every fallback reason without collapsing any two


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every fallback reason without collapsing any two")
var i = 1
var bad = 0
while i <= 8:
    val txt = stage_fallback_reason_to_text(
        stage_fallback_reason_from_u8(i))
    val d = decode_stage_receipt(encode_stage_receipt(
        fixture_stage_receipt(txt), ExecutionMode.HybridVectorGpu))
    if not d.ok:
        bad = bad + 1
    else:
        if d.value.fallback_reason != txt:
            bad = bad + 1
    i = i + 1
assert_equal(bad, 0)
```

</details>

#### round-trips a verification receipt including its origins handle

- round-trips a verification receipt including its origins handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a verification receipt including its origins handle")
val v = fixture_verification_mismatch()
val d = decode_verification_receipt(encode_verification_receipt(v))
assert_true(d.ok)
assert_true(verification_receipt_equal(d.value, v))
assert_true(mapping_shard_ref_equal(d.value.origins,
                                    fixture_shard_ref()))
```

</details>

#### round-trips a never-run verification receipt

- round-trips a never-run verification receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a never-run verification receipt")
val v = verification_receipt_not_run("layout", "cpu",
                                     ExecutionMode.CpuReference)
val d = decode_verification_receipt(encode_verification_receipt(v))
assert_true(d.ok)
assert_true(verification_receipt_equal(d.value, v))
```

</details>

### receipt decoders hard-reject malformed input

#### rejects an empty buffer for every record type

- rejects an empty buffer for every record type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty buffer for every record type")
val empty: [u8] = []
assert_false(decode_mapping_shard_ref(empty).ok)
assert_false(decode_stage_receipt(empty).ok)
assert_false(decode_verification_receipt(empty).ok)
```

</details>

#### rejects a stage receipt buffer offered to the other two decoders

- rejects a stage receipt buffer offered to the other two decoders


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a stage receipt buffer offered to the other two decoders")
val b = encode_stage_receipt(
    fixture_stage_receipt("device_lost"), ExecutionMode.HybridVectorGpu)
assert_false(decode_mapping_shard_ref(b).ok)
assert_false(decode_verification_receipt(b).ok)
```

</details>

#### rejects a wrong magic byte

- rejects a wrong magic byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong magic byte")
val b = encode_mapping_shard_ref(fixture_shard_ref())
assert_false(decode_mapping_shard_ref(corrupt_byte(b, 0, 0x54)).ok)
```

</details>

#### rejects a wrong schema version

- rejects a wrong schema version


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong schema version")
val b = encode_verification_receipt(fixture_verification_mismatch())
assert_false(decode_verification_receipt(corrupt_byte(b, 4, 2)).ok)
```

</details>

#### rejects a non-zero envelope reserved field

- rejects a non-zero envelope reserved field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a non-zero envelope reserved field")
val b = encode_verification_receipt(fixture_verification_mismatch())
assert_false(decode_verification_receipt(corrupt_byte(b, 6, 1)).ok)
```

</details>

#### rejects a truncated record rather than reading past the end

- rejects a truncated record rather than reading past the end


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated record rather than reading past the end")
val b = encode_stage_receipt(
    fixture_stage_receipt("device_lost"), ExecutionMode.HybridVectorGpu)
assert_false(decode_stage_receipt(truncated(b, 20)).ok)
assert_false(decode_stage_receipt(truncated(b, b.len() - 1)).ok)
```

</details>

#### rejects trailing bytes after a complete record

- rejects trailing bytes after a complete record


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trailing bytes after a complete record")
var b = encode_mapping_shard_ref(fixture_shard_ref())
b.push(0)
assert_false(decode_mapping_shard_ref(b).ok)
```

</details>

#### rejects an unknown ExecutionMode discriminant

- rejects an unknown ExecutionMode discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown ExecutionMode discriminant")
val b = encode_stage_receipt(
    fixture_stage_receipt("device_lost"), ExecutionMode.HybridVectorGpu)
assert_false(decode_stage_receipt(corrupt_byte(b, 13, 3)).ok)
```

</details>

#### rejects an unknown StageFallbackReason discriminant

- rejects an unknown StageFallbackReason discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown StageFallbackReason discriminant")
val b = encode_stage_receipt(
    fixture_stage_receipt("device_lost"), ExecutionMode.HybridVectorGpu)
assert_false(decode_stage_receipt(corrupt_byte(b, 14, 9)).ok)
```

</details>

#### rejects a forged buffer pairing a diverged mode with reason None

- rejects a forged buffer pairing a diverged mode with reason None


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a forged buffer pairing a diverged mode with reason None")
val b = encode_stage_receipt(
    fixture_stage_receipt("device_lost"), ExecutionMode.HybridVectorGpu)
# Byte 14 is fallback_reason; zeroing it claims no fallback happened
# while byte 12 still says HybridVectorGpu was requested and byte 13
# still says CpuReference ran. That is the silent fallback.
assert_false(decode_stage_receipt(corrupt_byte(b, 14, 0)).ok)
```

</details>

#### rejects an unknown VerificationPolicy or VerificationOutcome

- rejects an unknown VerificationPolicy or VerificationOutcome


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown VerificationPolicy or VerificationOutcome")
val b = encode_verification_receipt(fixture_verification_mismatch())
assert_false(decode_verification_receipt(corrupt_byte(b, 13, 5)).ok)
assert_false(decode_verification_receipt(corrupt_byte(b, 14, 4)).ok)
```

</details>

### receipt encoders refuse to emit a lying record

#### refuses a Mismatch that reports zero mismatches

- refuses a Mismatch that reports zero mismatches


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a Mismatch that reports zero mismatches")
val v = verification_receipt("layout", "gpu",
                             ExecutionMode.HybridVectorGpu,
                             VerificationPolicy.OracleCompare,
                             VerificationOutcome.Mismatch,
                             10, 0, entity_ref(0, 0), "", "",
                             mapping_shard_ref_none(), 0)
assert_false(verification_receipt_consistent(v))
assert_equal(encode_verification_receipt(v).len(), 0)
```

</details>

#### refuses a clean outcome that reports a non-zero mismatch count

- refuses a clean outcome that reports a non-zero mismatch count


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a clean outcome that reports a non-zero mismatch count")
val v = verification_receipt("layout", "gpu",
                             ExecutionMode.HybridVectorGpu,
                             VerificationPolicy.Full,
                             VerificationOutcome.Match,
                             10, 2, entity_ref(0, 0), "", "",
                             mapping_shard_ref_none(), 0)
assert_false(verification_receipt_consistent(v))
```

</details>

#### refuses more mismatches than checks

- refuses more mismatches than checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses more mismatches than checks")
val v = verification_receipt("layout", "gpu",
                             ExecutionMode.HybridVectorGpu,
                             VerificationPolicy.Full,
                             VerificationOutcome.Mismatch,
                             2, 5, entity_ref(0, 0), "", "",
                             mapping_shard_ref_none(), 0)
assert_false(verification_receipt_consistent(v))
```

</details>

#### refuses an oracle hash under a policy that consults no oracle

- refuses an oracle hash under a policy that consults no oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an oracle hash under a policy that consults no oracle")
val v = verification_receipt("layout", "gpu",
                             ExecutionMode.HybridVectorGpu,
                             VerificationPolicy.Full,
                             VerificationOutcome.Match,
                             10, 0, entity_ref(0, 0), "", "ad",
                             mapping_shard_ref_none(), 0)
assert_false(verification_receipt_consistent(v))
```

</details>

#### refuses a NotRun outcome that claims to have checked items

- refuses a NotRun outcome that claims to have checked items


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a NotRun outcome that claims to have checked items")
val v = verification_receipt("layout", "gpu",
                             ExecutionMode.HybridVectorGpu,
                             VerificationPolicy.Off,
                             VerificationOutcome.NotRun,
                             10, 0, entity_ref(0, 0), "", "",
                             mapping_shard_ref_none(), 0)
assert_false(verification_receipt_consistent(v))
```

</details>

#### accepts the consistent fixture it rejects the variants of

- accepts the consistent fixture it rejects the variants of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the consistent fixture it rejects the variants of")
assert_true(
    verification_receipt_consistent(fixture_verification_mismatch()))
```

</details>

#### refuses a non-ASCII text field rather than re-encoding it

- refuses a non-ASCII text field rather than re-encoding it


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a non-ASCII text field rather than re-encoding it")
assert_true(receipt_text_ascii("layout"))
assert_false(receipt_text_ascii("layoût"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/receipt_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ExecutionMode wire discriminants, StageFallbackReason vocabulary, VerificationPolicy and VerificationOutcome vocabularies, cpu_selected is distinguishable from gpu_fallback, MappingShardRef exact bytes, StageReceipt exact bytes, VerificationReceipt exact bytes, receipt round trips, receipt decoders hard-reject malformed input, receipt encoders refuse to emit a lying record.
- ExecutionMode wire discriminants
- StageFallbackReason vocabulary
- VerificationPolicy and VerificationOutcome vocabularies
- cpu_selected is distinguishable from gpu_fallback
- MappingShardRef exact bytes
- StageReceipt exact bytes
- VerificationReceipt exact bytes
- receipt round trips
- receipt decoders hard-reject malformed input
- receipt encoders refuse to emit a lying record

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 64 |
| Active scenarios | 64 |
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

- Canonical SPipe generation for source `df55005bfa30eecbfaa0d4c1377c2b85cb9012eb0e1ef1fd669121b0587cf601`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df55005bfa30eecbfaa0d4c1377c2b85cb9012eb0e1ef1fd669121b0587cf601`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df55005bfa30eecbfaa0d4c1377c2b85cb9012eb0e1ef1fd669121b0587cf601`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/receipt_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/receipt_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/receipt_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/receipt_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/receipt_contract_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns the three architecture variants to 0..2 in declaration order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/receipt_contract_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares exactly three modes with 2 as the maximum discriminant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/receipt_contract_spec.spl:197:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every discriminant through from_u8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
