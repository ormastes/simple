# hwir_retire_receipt_loopback_spec

> Exercise the bounded reset-coupled receipt transport without claiming a core.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_retire_receipt_loopback_spec

Exercise the bounded reset-coupled receipt transport without claiming a core.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercise the bounded reset-coupled receipt transport without claiming a core.

The loopback is intentionally a host verification model.  These checks prove
only its typed, one-entry transport behavior and explicitly reject use as an
architectural retirement emitter or certificate.

## Scenarios

### RISC-V Gen2 verification-only retirement receipt loopback

#### should preserve one accepted RV32 and RV64 identity tuple for exactly one post-dispatch cycle

- should preserve one accepted RV32 and RV64 identity tuple for exactly one post-dispatch cycle
- Capture and return one typed receipt for each concrete mission-critical configuration
   - Expected: accepted.dispatch_accept equals `1`
   - Expected: accepted.retire_valid equals `0`
   - Expected: accepted.next_state.pending equals `1`
   - Expected: retired.dispatch_accept equals `0`
   - Expected: retired.retire_valid equals `1`
   - Expected: retired.retire_lineage equals `19`
   - Expected: retired.retire_original_parcel equals `0x9002`
   - Expected: retired.retire_canonical_instruction equals `0x001000ef`
   - Expected: retired.retire_original_length_bytes equals `2`
   - Expected: retired.next_state.pending equals `0`
   - Expected: repeated.retire_valid equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should preserve one accepted RV32 and RV64 identity tuple for exactly one post-dispatch cycle")
step("Capture and return one typed receipt for each concrete mission-critical configuration")
for config in [CoreConfig.rv32_zca_cjal_mission_critical(),
    CoreConfig.rv64_zca_addiw_mission_critical()]:
    val plan = strict_riscv_retire_receipt_loopback_plan(config).unwrap()
    val initial = strict_riscv_retire_receipt_loopback_initial_state(plan).unwrap()
    val accepted = advance_strict_riscv_retire_receipt_loopback(plan, initial,
        dispatch(19, 0x9002, 0x001000ef, 2)).unwrap()
    expect(accepted.dispatch_accept).to_equal(1)
    expect(accepted.retire_valid).to_equal(0)
    expect(accepted.next_state.pending).to_equal(1)
    val retired = advance_strict_riscv_retire_receipt_loopback(plan,
        accepted.next_state, HwRetireReceiptLoopbackInput.idle()).unwrap()
    expect(retired.dispatch_accept).to_equal(0)
    expect(retired.retire_valid).to_equal(1)
    expect(retired.retire_lineage).to_equal(19)
    expect(retired.retire_original_parcel).to_equal(0x9002)
    expect(retired.retire_canonical_instruction).to_equal(0x001000ef)
    expect(retired.retire_original_length_bytes).to_equal(2)
    expect(retired.next_state.pending).to_equal(0)
    val repeated = advance_strict_riscv_retire_receipt_loopback(plan,
        retired.next_state, HwRetireReceiptLoopbackInput.idle()).unwrap()
    expect(repeated.retire_valid).to_equal(0)
```

</details>

#### should give synchronous reset priority and cannot replay a pre-reset receipt

- should give synchronous reset priority and cannot replay a pre-reset receipt
- Reset a pending receipt then retire only a new post-reset identity
   - Expected: reset.dispatch_accept equals `0`
   - Expected: reset.retire_valid equals `0`
   - Expected: reset.next_state.pending equals `0`
   - Expected: after_reset.retire_valid equals `0`
   - Expected: new_retired.retire_lineage equals `8`
   - Expected: new_retired.retire_original_parcel equals `0x9002`
   - Expected: new_retired.retire_canonical_instruction equals `0x001000ef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should give synchronous reset priority and cannot replay a pre-reset receipt")
step("Reset a pending receipt then retire only a new post-reset identity")
val plan = strict_riscv_retire_receipt_loopback_plan(
    CoreConfig.rv32_zca_cjal_mission_critical()).unwrap()
val initial = strict_riscv_retire_receipt_loopback_initial_state(plan).unwrap()
val pending = advance_strict_riscv_retire_receipt_loopback(plan, initial,
    dispatch(7, 0x8082, 0x00008067, 2)).unwrap()
val reset = advance_strict_riscv_retire_receipt_loopback(plan, pending.next_state,
    HwRetireReceiptLoopbackInput.reset()).unwrap()
expect(reset.dispatch_accept).to_equal(0)
expect(reset.retire_valid).to_equal(0)
expect(reset.next_state.pending).to_equal(0)
val after_reset = advance_strict_riscv_retire_receipt_loopback(plan, reset.next_state,
    HwRetireReceiptLoopbackInput.idle()).unwrap()
expect(after_reset.retire_valid).to_equal(0)
val new_pending = advance_strict_riscv_retire_receipt_loopback(plan, after_reset.next_state,
    dispatch(8, 0x9002, 0x001000ef, 2)).unwrap()
val new_retired = advance_strict_riscv_retire_receipt_loopback(plan,
    new_pending.next_state, HwRetireReceiptLoopbackInput.idle()).unwrap()
expect(new_retired.retire_lineage).to_equal(8)
expect(new_retired.retire_original_parcel).to_equal(0x9002)
expect(new_retired.retire_canonical_instruction).to_equal(0x001000ef)
```

</details>

#### should discard a simultaneous dispatch on reset and erase every invalid receipt field

- should discard a simultaneous dispatch on reset and erase every invalid receipt field
- Assert reset with a valid dispatch while a distinct receipt is pending
   - Expected: reset.dispatch_accept equals `0`
   - Expected: reset.retire_valid equals `0`
   - Expected: reset.retire_lineage equals `0`
   - Expected: reset.retire_original_parcel equals `0`
   - Expected: reset.retire_canonical_instruction equals `0`
   - Expected: reset.retire_original_length_bytes equals `0`
   - Expected: reset.next_state.pending equals `0`
   - Expected: reset.next_state.lineage equals `0`
   - Expected: idle.retire_valid equals `0`
   - Expected: idle.retire_lineage equals `0`
   - Expected: idle.retire_original_parcel equals `0`
   - Expected: idle.retire_canonical_instruction equals `0`
   - Expected: idle.retire_original_length_bytes equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should discard a simultaneous dispatch on reset and erase every invalid receipt field")
step("Assert reset with a valid dispatch while a distinct receipt is pending")
val plan = strict_riscv_retire_receipt_loopback_plan(
    CoreConfig.rv64_zca_addiw_mission_critical()).unwrap()
val initial = strict_riscv_retire_receipt_loopback_initial_state(plan).unwrap()
val pending = advance_strict_riscv_retire_receipt_loopback(plan, initial,
    dispatch(41, 0x8082, 0x00008067, 2)).unwrap()
val reset_with_dispatch = HwRetireReceiptLoopbackInput(rst: 1, dispatch_valid: 1,
    dispatch_lineage: 42, dispatch_original_parcel: 0x9002,
    dispatch_canonical_instruction: 0x001000ef, dispatch_original_length_bytes: 2)
val reset = advance_strict_riscv_retire_receipt_loopback(plan, pending.next_state,
    reset_with_dispatch).unwrap()
expect(reset.dispatch_accept).to_equal(0)
expect(reset.retire_valid).to_equal(0)
expect(reset.retire_lineage).to_equal(0)
expect(reset.retire_original_parcel).to_equal(0)
expect(reset.retire_canonical_instruction).to_equal(0)
expect(reset.retire_original_length_bytes).to_equal(0)
expect(reset.next_state.pending).to_equal(0)
expect(reset.next_state.lineage).to_equal(0)
val idle = advance_strict_riscv_retire_receipt_loopback(plan, reset.next_state,
    HwRetireReceiptLoopbackInput.idle()).unwrap()
expect(idle.retire_valid).to_equal(0)
expect(idle.retire_lineage).to_equal(0)
expect(idle.retire_original_parcel).to_equal(0)
expect(idle.retire_canonical_instruction).to_equal(0)
expect(idle.retire_original_length_bytes).to_equal(0)
```

</details>

#### should stall a competing dispatch while returning the pending receipt exactly once

- should stall a competing dispatch while returning the pending receipt exactly once
- Attempt a second dispatch in the pending receipt cycle
   - Expected: competing.dispatch_accept equals `0`
   - Expected: competing.retire_valid equals `1`
   - Expected: competing.retire_lineage equals `51`
   - Expected: competing.retire_original_parcel equals `0x9002`
   - Expected: competing.retire_canonical_instruction equals `0x001000ef`
   - Expected: competing.next_state.pending equals `0`
   - Expected: no_competing_receipt.dispatch_accept equals `0`
   - Expected: no_competing_receipt.retire_valid equals `0`
   - Expected: no_competing_receipt.retire_lineage equals `0`
   - Expected: no_competing_receipt.retire_original_parcel equals `0`
   - Expected: no_competing_receipt.retire_canonical_instruction equals `0`
   - Expected: no_competing_receipt.retire_original_length_bytes equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should stall a competing dispatch while returning the pending receipt exactly once")
step("Attempt a second dispatch in the pending receipt cycle")
val plan = strict_riscv_retire_receipt_loopback_plan(
    CoreConfig.rv32_zca_cjal_mission_critical()).unwrap()
val initial = strict_riscv_retire_receipt_loopback_initial_state(plan).unwrap()
val first = advance_strict_riscv_retire_receipt_loopback(plan, initial,
    dispatch(51, 0x9002, 0x001000ef, 2)).unwrap()
val competing = advance_strict_riscv_retire_receipt_loopback(plan, first.next_state,
    dispatch(52, 0x8082, 0x00008067, 2)).unwrap()
expect(competing.dispatch_accept).to_equal(0)
expect(competing.retire_valid).to_equal(1)
expect(competing.retire_lineage).to_equal(51)
expect(competing.retire_original_parcel).to_equal(0x9002)
expect(competing.retire_canonical_instruction).to_equal(0x001000ef)
expect(competing.next_state.pending).to_equal(0)
val no_competing_receipt = advance_strict_riscv_retire_receipt_loopback(plan,
    competing.next_state, HwRetireReceiptLoopbackInput.idle()).unwrap()
expect(no_competing_receipt.dispatch_accept).to_equal(0)
expect(no_competing_receipt.retire_valid).to_equal(0)
expect(no_competing_receipt.retire_lineage).to_equal(0)
expect(no_competing_receipt.retire_original_parcel).to_equal(0)
expect(no_competing_receipt.retire_canonical_instruction).to_equal(0)
expect(no_competing_receipt.retire_original_length_bytes).to_equal(0)
```

</details>

#### should reject malformed plan configurations and producer contracts before any cycle advances

- should reject malformed plan configurations and producer contracts before any cycle advances
- Corrupt each closed plan boundary and require its typed diagnostic
   - Expected: invalid_config_result.is_ok() is false
   - Expected: malformed_producer_result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject malformed plan configurations and producer contracts before any cycle advances")
step("Corrupt each closed plan boundary and require its typed diagnostic")
val invalid_config = strict_riscv_retire_receipt_loopback_plan(
    CoreConfig.rv32_zca_cjal_mission_critical()).unwrap()
invalid_config.config.xlen = 16
val invalid_config_result = strict_riscv_retire_receipt_loopback_initial_state(invalid_config)
expect(invalid_config_result.is_ok()).to_equal(false)
expect(invalid_config_result.err()).to_equal(
    "HWIR-E-CONFIG-XLEN: strict RISC-V HWIR requires XLEN=32 or XLEN=64")
val mismatched_config = strict_riscv_retire_receipt_loopback_plan(
    CoreConfig.rv32_zca_cjal_mission_critical()).unwrap()
mismatched_config.producer.config = CoreConfig.rv64_zca_addiw_mission_critical()
expect(mismatched_config.shape_diagnostic()).to_equal(
    "HWIR-E-RETIRE-LOOPBACK-CONFIG: verification loopback and producer require one concrete product configuration")
val malformed_producer = strict_riscv_retire_receipt_loopback_plan(
    CoreConfig.rv64_zca_addiw_mission_critical()).unwrap()
malformed_producer.producer.retire_valid.bit_width = 2
val malformed_producer_result = strict_riscv_retire_receipt_loopback_initial_state(malformed_producer)
expect(malformed_producer_result.is_ok()).to_equal(false)
expect(malformed_producer_result.err()).to_equal(
    "HWIR-E-RETIRE-PRODUCER-RECEIPT-WIDTH: retirement producer must publish the exact receipt identity tuple")
val unsafe_scope = strict_riscv_retire_receipt_loopback_plan(
    CoreConfig.rv64_zca_addiw_mission_critical()).unwrap()
unsafe_scope.maximum_inflight = 2
expect(unsafe_scope.shape_diagnostic()).to_equal(
    "HWIR-E-RETIRE-LOOPBACK-SCOPE: loopback is a closed one-entry one-cycle verification-only plan")
```

</details>

#### should reject malformed synchronous inputs and stale empty-slot state

- should reject malformed synchronous inputs and stale empty-slot state
- Fail closed before accepting invalid one-bit, tuple-width, or empty-slot values
   - Expected: invalid_valid_result.is_ok() is false
   - Expected: oversized_tuple_result.is_ok() is false
   - Expected: stale_empty_slot_result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject malformed synchronous inputs and stale empty-slot state")
step("Fail closed before accepting invalid one-bit, tuple-width, or empty-slot values")
val plan = strict_riscv_retire_receipt_loopback_plan(
    CoreConfig.rv32_zca_cjal_mission_critical()).unwrap()
val initial = strict_riscv_retire_receipt_loopback_initial_state(plan).unwrap()
val invalid_valid = HwRetireReceiptLoopbackInput(rst: 0, dispatch_valid: 2,
    dispatch_lineage: 0, dispatch_original_parcel: 0, dispatch_canonical_instruction: 0,
    dispatch_original_length_bytes: 0)
val invalid_valid_result = advance_strict_riscv_retire_receipt_loopback(plan, initial,
    invalid_valid)
expect(invalid_valid_result.is_ok()).to_equal(false)
expect(invalid_valid_result.err()).to_equal(
    "HWIR-E-RETIRE-LOOPBACK-INPUT: reset and dispatch valid must be one-bit values")
val oversized_tuple = HwRetireReceiptLoopbackInput(rst: 0, dispatch_valid: 1,
    dispatch_lineage: 0, dispatch_original_parcel: 65536,
    dispatch_canonical_instruction: 4294967296, dispatch_original_length_bytes: 4)
val oversized_tuple_result = advance_strict_riscv_retire_receipt_loopback(plan, initial,
    oversized_tuple)
expect(oversized_tuple_result.is_ok()).to_equal(false)
expect(oversized_tuple_result.err()).to_equal(
    "HWIR-E-RETIRE-LOOPBACK-INPUT: dispatch fields must fit the typed identity tuple")
val stale_empty_slot = HwRetireReceiptLoopbackState(pending: 0, lineage: 1,
    original_parcel: 0, canonical_instruction: 0, original_length_bytes: 0)
val stale_empty_slot_result = advance_strict_riscv_retire_receipt_loopback(plan,
    stale_empty_slot, HwRetireReceiptLoopbackInput.idle())
expect(stale_empty_slot_result.is_ok()).to_equal(false)
expect(stale_empty_slot_result.err()).to_equal(
    "HWIR-E-RETIRE-LOOPBACK-STATE: an empty loopback slot must erase retained receipt identity")
```

</details>

#### should fail closed outside the one-entry verification-only transport boundary

- should fail closed outside the one-entry verification-only transport boundary
- Reject a production-shaped plan and malformed typed dispatch values
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should fail closed outside the one-entry verification-only transport boundary")
step("Reject a production-shaped plan and malformed typed dispatch values")
val plan = strict_riscv_retire_receipt_loopback_plan(
    CoreConfig.rv64_zca_addiw_mission_critical()).unwrap()
val initial = strict_riscv_retire_receipt_loopback_initial_state(plan).unwrap()
expect(plan.production_diagnostic()).to_equal(
    "HWIR-E-RETIRE-LOOPBACK-VERIFICATION-ONLY: loopback plan cannot emit or certify an architectural retirement producer")
val bad_plan = strict_riscv_retire_receipt_loopback_plan(
    CoreConfig.rv64_zca_addiw_mission_critical()).unwrap()
bad_plan.verification_only = false
expect(bad_plan.shape_diagnostic()).to_equal(
    "HWIR-E-RETIRE-LOOPBACK-SCOPE: loopback is a closed one-entry one-cycle verification-only plan")
val malformed = HwRetireReceiptLoopbackInput(rst: 0, dispatch_valid: 1,
    dispatch_lineage: -1, dispatch_original_parcel: 0, dispatch_canonical_instruction: 0,
    dispatch_original_length_bytes: 2)
val result = advance_strict_riscv_retire_receipt_loopback(plan, initial, malformed)
expect(result.is_ok()).to_equal(false)
expect(result.err()).to_equal(
    "HWIR-E-RETIRE-LOOPBACK-INPUT: dispatch fields must fit the typed identity tuple")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `afe7a4c81efe4b5f55ae8f518f90ac4e26d47112b81452c46885ef098bed3c7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `afe7a4c81efe4b5f55ae8f518f90ac4e26d47112b81452c46885ef098bed3c7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `afe7a4c81efe4b5f55ae8f518f90ac4e26d47112b81452c46885ef098bed3c7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 37 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve one accepted RV32 and RV64 identity tuple for exactly one post-dispatch cycle' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve one accepted RV32 and RV64 identity tuple for exactly one post-dispatch cycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should give synchronous reset priority and cannot replay a pre-reset receipt' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should give synchronous reset priority and cannot replay a pre-reset receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should discard a simultaneous dispatch on reset and erase every invalid receipt field' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should discard a simultaneous dispatch on reset and erase every invalid receipt field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl:115:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stall a competing dispatch while returning the pending receipt exactly once' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl:142:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed plan configurations and producer contracts before any cycle advances' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl:172:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed synchronous inputs and stale empty-slot state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
