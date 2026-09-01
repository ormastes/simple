# hwir_host_evaluator_spec

> Execute the exact strict combinational graph for composed-predecode oracles.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_host_evaluator_spec

Execute the exact strict combinational graph for composed-predecode oracles.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Execute the exact strict combinational graph for composed-predecode oracles.

## Scenarios

### RISC-V Gen2 strict HWIR host evaluator

#### should evaluate the exact RV32 and RV64 C.EBREAK trap tuple

- should evaluate the exact RV32 and RV64 C.EBREAK trap tuple
- Build each concrete target-trap graph and execute its typed operations
   - Expected: result.value_of("original_parcel").unwrap() equals `0x9002`
   - Expected: result.value_of("canonical_instruction").unwrap() equals `0x00100073`
   - Expected: result.value_of("original_length_bytes").unwrap() equals `2`
   - Expected: result.value_of("legal").unwrap() equals `1`
   - Expected: result.value_of("next_pc").unwrap() equals `0x122`
   - Expected: result.value_of("redirect_valid").unwrap() equals `0`
   - Expected: result.value_of("redirect_target").unwrap() equals `0x120`
   - Expected: result.value_of("trap_valid").unwrap() equals `1`
   - Expected: result.value_of("trap_cause").unwrap() equals `3`
   - Expected: result.value_of("trap_tval").unwrap() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should evaluate the exact RV32 and RV64 C.EBREAK trap tuple")
step("Build each concrete target-trap graph and execute its typed operations")
for config in [CoreConfig.rv32_zca_cjal_mission_critical(),
    CoreConfig.rv64_zca_addiw_mission_critical()]:
    val result = evaluate_strict_comb_hwir(target_trap_module(config),
        target_trap_inputs(0x9002, 0x120, 8, 0)).unwrap()
    expect(result.value_of("original_parcel").unwrap()).to_equal(0x9002)
    expect(result.value_of("canonical_instruction").unwrap()).to_equal(0x00100073)
    expect(result.value_of("original_length_bytes").unwrap()).to_equal(2)
    expect(result.value_of("legal").unwrap()).to_equal(1)
    expect(result.value_of("next_pc").unwrap()).to_equal(0x122)
    expect(result.value_of("redirect_valid").unwrap()).to_equal(0)
    expect(result.value_of("redirect_target").unwrap()).to_equal(0x120)
    expect(result.value_of("trap_valid").unwrap()).to_equal(1)
    expect(result.value_of("trap_cause").unwrap()).to_equal(3)
    expect(result.value_of("trap_tval").unwrap()).to_equal(0)
```

</details>

#### should prepare one deterministic schedule for repeated concrete parcels

- should prepare one deterministic schedule for repeated concrete parcels
- Resolve the target-trap graph once before varying its parcel input
   - Expected: first.value_of("canonical_instruction").unwrap() equals `0x000000ef`
   - Expected: first.value_of("redirect_valid").unwrap() equals `1`
   - Expected: second.value_of("canonical_instruction").unwrap() equals `0x00100073`
   - Expected: second.value_of("trap_valid").unwrap() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should prepare one deterministic schedule for repeated concrete parcels")
step("Resolve the target-trap graph once before varying its parcel input")
val prepared = prepare_strict_comb_hwir(
    target_trap_module(CoreConfig.rv32_zca_cjal_mission_critical())).unwrap()
val first = prepared.evaluate(target_trap_inputs(0x2001, 0x100, 0, 0)).unwrap()
val second = prepared.evaluate(target_trap_inputs(0x9002, 0x100, 0, 0)).unwrap()
expect(first.value_of("canonical_instruction").unwrap()).to_equal(0x000000ef)
expect(first.value_of("redirect_valid").unwrap()).to_equal(1)
expect(second.value_of("canonical_instruction").unwrap()).to_equal(0x00100073)
expect(second.value_of("trap_valid").unwrap()).to_equal(1)
```

</details>

#### should fail closed for an unsupported parcel through the composed graph

- should fail closed for an unsupported parcel through the composed graph
- Execute the target-trap graph rather than an independent decoder classifier
   - Expected: result.value_of("canonical_instruction").unwrap() equals `0`
   - Expected: result.value_of("legal").unwrap() equals `0`
   - Expected: result.value_of("next_pc").unwrap() equals `0x342`
   - Expected: result.value_of("redirect_valid").unwrap() equals `0`
   - Expected: result.value_of("redirect_target").unwrap() equals `0x340`
   - Expected: result.value_of("trap_valid").unwrap() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should fail closed for an unsupported parcel through the composed graph")
step("Execute the target-trap graph rather than an independent decoder classifier")
for config in [CoreConfig.rv32_zca_cjal_mission_critical(),
    CoreConfig.rv64_zca_addiw_mission_critical()]:
    val result = evaluate_strict_comb_hwir(target_trap_module(config),
        target_trap_inputs(0, 0x340, 8, 0)).unwrap()
    expect(result.value_of("canonical_instruction").unwrap()).to_equal(0)
    expect(result.value_of("legal").unwrap()).to_equal(0)
    expect(result.value_of("next_pc").unwrap()).to_equal(0x342)
    expect(result.value_of("redirect_valid").unwrap()).to_equal(0)
    expect(result.value_of("redirect_target").unwrap()).to_equal(0x340)
    expect(result.value_of("trap_valid").unwrap()).to_equal(0)
```

</details>

#### should execute the distinct RV32 C.JAL and RV64 C.ADDIW target rows

- should execute the distinct RV32 C.JAL and RV64 C.ADDIW target rows
- Evaluate the target-specific parcel class through each selected graph
   - Expected: rv32.value_of("legal").unwrap() equals `1`
   - Expected: rv32.value_of("canonical_instruction").unwrap() equals `0x000000ef`
   - Expected: rv32.value_of("redirect_valid").unwrap() equals `1`
   - Expected: rv32.value_of("next_pc").unwrap() equals `0x180`
   - Expected: rv32.value_of("trap_valid").unwrap() equals `0`
   - Expected: rv64.value_of("legal").unwrap() equals `1`
   - Expected: rv64.value_of("canonical_instruction").unwrap() equals `0x0010809b`
   - Expected: rv64.value_of("redirect_valid").unwrap() equals `0`
   - Expected: rv64.value_of("next_pc").unwrap() equals `0x1a2`
   - Expected: rv64.value_of("trap_valid").unwrap() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should execute the distinct RV32 C.JAL and RV64 C.ADDIW target rows")
step("Evaluate the target-specific parcel class through each selected graph")
val rv32 = evaluate_strict_comb_hwir(
    target_trap_module(CoreConfig.rv32_zca_cjal_mission_critical()),
    target_trap_inputs(0x2001, 0x180, 0, 0)).unwrap()
expect(rv32.value_of("legal").unwrap()).to_equal(1)
expect(rv32.value_of("canonical_instruction").unwrap()).to_equal(0x000000ef)
expect(rv32.value_of("redirect_valid").unwrap()).to_equal(1)
expect(rv32.value_of("next_pc").unwrap()).to_equal(0x180)
expect(rv32.value_of("trap_valid").unwrap()).to_equal(0)
val rv64 = evaluate_strict_comb_hwir(
    target_trap_module(CoreConfig.rv64_zca_addiw_mission_critical()),
    target_trap_inputs(0x2085, 0x1a0, 1, 0)).unwrap()
expect(rv64.value_of("legal").unwrap()).to_equal(1)
expect(rv64.value_of("canonical_instruction").unwrap()).to_equal(0x0010809b)
expect(rv64.value_of("redirect_valid").unwrap()).to_equal(0)
expect(rv64.value_of("next_pc").unwrap()).to_equal(0x1a2)
expect(rv64.value_of("trap_valid").unwrap()).to_equal(0)
```

</details>

#### should preserve a PA64 high-bit indirect JALR target as a logical shift

- should preserve a PA64 high-bit indirect JALR target as a logical shift
- Use an allowed PA64 RV64 product to expose unsigned shift-right semantics
   - Expected: result.value_of("legal").unwrap() equals `1`
   - Expected: result.value_of("canonical_instruction").unwrap() equals `0x00008067`
   - Expected: result.value_of("redirect_valid").unwrap() equals `1`
   - Expected: result.value_of("redirect_target").unwrap() equals `-9223372036854775806`
   - Expected: result.value_of("next_pc").unwrap() equals `-9223372036854775806`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should preserve a PA64 high-bit indirect JALR target as a logical shift")
step("Use an allowed PA64 RV64 product to expose unsigned shift-right semantics")
val config = CoreConfig(xlen: 64, physical_address_bits: 64, register_count: 32,
    profile: "riscv-gen2-rv64-zca-addiw-critical", isa_profile: "rv64i_zca",
    compressed_decode_profile: "zca-common-critical")
val result = evaluate_strict_comb_hwir(target_trap_module(config),
    target_trap_inputs(0x8082, 0x80, 1, -9223372036854775805)).unwrap()
expect(result.value_of("legal").unwrap()).to_equal(1)
expect(result.value_of("canonical_instruction").unwrap()).to_equal(0x00008067)
expect(result.value_of("redirect_valid").unwrap()).to_equal(1)
expect(result.value_of("redirect_target").unwrap()).to_equal(-9223372036854775806)
expect(result.value_of("next_pc").unwrap()).to_equal(-9223372036854775806)
```

</details>

#### should reject missing or non-input host values before graph execution

- should reject missing or non-input host values before graph execution
- Prove the evaluator cannot silently fabricate a register operand


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject missing or non-input host values before graph execution")
step("Prove the evaluator cannot silently fabricate a register operand")
val module = target_trap_module(CoreConfig.rv32_zca_cjal_mission_critical())
val missing = evaluate_strict_comb_hwir(module,
    [HwHostInput.bits("original_parcel", 0x9002), HwHostInput.bits("fetch_pc", 0),
        HwHostInput.bits("rs1_index", 8)])
expect(missing.err().unwrap()).to_contain("HWIR-E-HOST-EVAL-INPUT")
val output_as_input = evaluate_strict_comb_hwir(module,
    [HwHostInput.bits("original_parcel", 0x9002), HwHostInput.bits("fetch_pc", 0),
        HwHostInput.bits("rs1_index", 8), HwHostInput.bits("rs1_value", 0),
        HwHostInput.bits("legal", 1)])
expect(output_as_input.err().unwrap()).to_contain("HWIR-E-HOST-EVAL-INPUT")
```

</details>

#### should reject empty and duplicate host inputs before any result is produced

- should reject empty and duplicate host inputs before any result is produced
- Prepare the concrete graph once and present malformed host input tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject empty and duplicate host inputs before any result is produced")
step("Prepare the concrete graph once and present malformed host input tuples")
val prepared = prepare_strict_comb_hwir(
    target_trap_module(CoreConfig.rv32_zca_cjal_mission_critical())).unwrap()
val empty_name = prepared.evaluate([
    HwHostInput.bits("original_parcel", 0x9002), HwHostInput.bits("fetch_pc", 0),
    HwHostInput.bits("rs1_index", 8), HwHostInput.bits("", 0)])
expect(empty_name.err().unwrap()).to_start_with("HWIR-E-HOST-EVAL-INPUT")
val duplicate = prepared.evaluate([
    HwHostInput.bits("original_parcel", 0x9002), HwHostInput.bits("fetch_pc", 0),
    HwHostInput.bits("rs1_index", 8), HwHostInput.bits("rs1_value", 0),
    HwHostInput.bits("fetch_pc", 2)])
expect(duplicate.err().unwrap()).to_start_with("HWIR-E-HOST-EVAL-INPUT")
```

</details>

#### should normalize inputs and evaluate both equality and mux outcomes

- should normalize inputs and evaluate both equality and mux outcomes
- Evaluate a compact strict graph through both compare and select branches
   - Expected: choose_lhs.value_of("sum").unwrap() equals `2`
   - Expected: choose_lhs.value_of("equal").unwrap() equals `0`
   - Expected: choose_lhs.value_of("selected").unwrap() equals `15`
   - Expected: choose_rhs_equal.value_of("sum").unwrap() equals `6`
   - Expected: choose_rhs_equal.value_of("equal").unwrap() equals `1`
   - Expected: choose_rhs_equal.value_of("selected").unwrap() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should normalize inputs and evaluate both equality and mux outcomes")
step("Evaluate a compact strict graph through both compare and select branches")
val prepared = prepare_strict_comb_hwir(host_evaluator_mixed_module()).unwrap()
val choose_lhs = prepared.evaluate([
    HwHostInput.bits("lhs", 0x1f), HwHostInput.bits("rhs", 3),
    HwHostInput.bits("choose_lhs", 1)]).unwrap()
expect(choose_lhs.value_of("sum").unwrap()).to_equal(2)
expect(choose_lhs.value_of("equal").unwrap()).to_equal(0)
expect(choose_lhs.value_of("selected").unwrap()).to_equal(15)
val choose_rhs_equal = prepared.evaluate([
    HwHostInput.bits("lhs", 3), HwHostInput.bits("rhs", 3),
    HwHostInput.bits("choose_lhs", 0)]).unwrap()
expect(choose_rhs_equal.value_of("sum").unwrap()).to_equal(6)
expect(choose_rhs_equal.value_of("equal").unwrap()).to_equal(1)
expect(choose_rhs_equal.value_of("selected").unwrap()).to_equal(3)
```

</details>

#### should reject unsupported, width-invalid, and unreadable self-referential strict graphs before scheduling

- should reject unsupported, width-invalid, and unreadable self-referential strict graphs before scheduling
- Mutate independent typed graphs at the strict validation boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject unsupported, width-invalid, and unreadable self-referential strict graphs before scheduling")
step("Mutate independent typed graphs at the strict validation boundary")
val unsupported = host_evaluator_mixed_module()
unsupported.comb_ops[0].op = "not_a_strict_op"
expect(prepare_strict_comb_hwir(unsupported).err().unwrap()).to_start_with("HWIR-E-COMB")
val wrong_width = host_evaluator_mixed_module()
wrong_width.comb_ops[0].bit_width = 3
expect(prepare_strict_comb_hwir(wrong_width).err().unwrap()).to_start_with("HWIR-E-COMB")
val cycle = host_evaluator_mixed_module()
cycle.comb_ops[0].lhs = "sum"
expect(prepare_strict_comb_hwir(cycle).err().unwrap()).to_start_with("HWIR-E-OP-OPERAND-DIRECTION")
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `65ea9de4b4c21c1fd95dfa0e24ef90b176aba4c171f79931c6168fc321951f65`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65ea9de4b4c21c1fd95dfa0e24ef90b176aba4c171f79931c6168fc321951f65`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65ea9de4b4c21c1fd95dfa0e24ef90b176aba4c171f79931c6168fc321951f65`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_host_evaluator_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_host_evaluator_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_host_evaluator_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should evaluate the exact RV32 and RV64 C.EBREAK trap tuple' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should evaluate the exact RV32 and RV64 C.EBREAK trap tuple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prepare one deterministic schedule for repeated concrete parcels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should prepare one deterministic schedule for repeated concrete parcels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed for an unsupported parcel through the composed graph' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed for an unsupported parcel through the composed graph' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl:100:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the distinct RV32 C.JAL and RV64 C.ADDIW target rows' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl:122:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve a PA64 high-bit indirect JALR target as a logical shift' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl:138:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing or non-input host values before graph execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
