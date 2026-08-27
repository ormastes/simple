# Hwir Mixed Sequential Datapath Specification

> Tests covering mixed sequential HWIR datapath and explicit LSU geometry.

## Purpose and scope

This focused source-level unit specification constructs one RV32 strict
sequential HWIR module whose combinational datapath feeds guarded state. It
checks the emitted VHDL text for a typed 32-bit add, 8-bit truncation, 32-bit
sign extension, equality comparison, mux selection, and the selected value's
assignment into the state register. It also checks that explicit LSU bus and
mask geometry is validated independently of the selected core width and that
the RV32/RV64 product defaults expose their respective bus widths.

# Hwir Mixed Sequential Datapath Specification

## Scenarios

### mixed sequential HWIR datapath and explicit LSU geometry

## Requirement traceability

- should render typed add truncate sign extension compare and select before state
- Construct a typed combinational datapath feeding guarded sequential state
   - Expected: module.diagnostic() equals ``
   - Expected: emitted.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should render typed add truncate sign extension compare and select before state")
step("Construct a typed combinational datapath feeding guarded sequential state")
val module = mixed_module()
expect(module.diagnostic()).to_equal("")
val emitted = render_strict_sequential_hwir(module, "hwir-mixed-sequential-v1")
expect(emitted.is_success()).to_equal(true)
expect(emitted.vhdl).to_contain("sum <= std_logic_vector(unsigned(lhs) + unsigned(rhs));")
expect(emitted.vhdl).to_contain("low_byte <= std_logic_vector(resize(unsigned(sum), 8));")
expect(emitted.vhdl).to_contain("signed_byte <= std_logic_vector(resize(signed(low_byte), 32));")
expect(emitted.vhdl).to_contain("equal_value <= '1' when lhs = rhs else '0';")
expect(emitted.vhdl).to_contain("selected <= signed_byte when equal_value = '1' else zero32;")
expect(emitted.vhdl).to_contain("constant ones8 : std_logic_vector(7 downto 0) := \"11111111\";")
expect(emitted.vhdl).to_contain("sum_bit <= sum(0);")
expect(emitted.vhdl).to_contain("sum_high <= sum(31 downto 24);")
expect(emitted.vhdl).to_contain("value_reg <= selected;")
val datapath_index = emitted.vhdl.index_of("sum <=") ?? -1
val process_index = emitted.vhdl.index_of("process(clk)") ?? -1
expect(datapath_index).to_be_greater_than(-1)
expect(process_index).to_be_greater_than(datapath_index)
```

</details>

#### should validate LSU bus and mask widths independently of core widths

- should validate LSU bus and mask widths independently of core widths
- Validate explicit LSU transport geometry without inferring it from XLEN
   - Expected: LsuConfig.explicit(64, 8).is_ok() is true
   - Expected: LsuConfig.explicit(64, 4).is_err() is true
   - Expected: LsuConfig.explicit(48, 6).is_err() is true
   - Expected: LsuConfig.rv32_product_default().bus_data_bits equals `32`
   - Expected: LsuConfig.rv64_product_default().bus_data_bits equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should validate LSU bus and mask widths independently of core widths")
step("Validate explicit LSU transport geometry without inferring it from XLEN")
expect(LsuConfig.explicit(64, 8).is_ok()).to_equal(true)
expect(LsuConfig.explicit(64, 4).is_err()).to_equal(true)
expect(LsuConfig.explicit(48, 6).is_err()).to_equal(true)
expect(LsuConfig.rv32_product_default().bus_data_bits).to_equal(32)
expect(LsuConfig.rv64_product_default().bus_data_bits).to_equal(64)
```

</details>

#### should accept an XLEN unsigned predicate with a one-bit result

- should accept an XLEN unsigned predicate with a one-bit result
- Render an XLEN-wide unsigned predicate into a one-bit VHDL result
   - Expected: module.diagnostic() equals ``
   - Expected: emitted.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should accept an XLEN unsigned predicate with a one-bit result")
step("Render an XLEN-wide unsigned predicate into a one-bit VHDL result")
val module = unsigned_predicate_module()
expect(module.diagnostic()).to_equal("")
val emitted = render_strict_sequential_hwir(module,
    "hwir-mixed-sequential-predicate-v1")
expect(emitted.is_success()).to_equal(true)
expect(emitted.vhdl).to_contain(
    "lhs_uge_rhs <= '1' when unsigned(lhs) >= unsigned(rhs) else '0';")
```

</details>

#### should reject unsupported unreadable and duplicate datapath drivers

- should reject unsupported unreadable and duplicate datapath drivers
- Reject unsupported operations, unreadable values, and multiple drivers


<details>
<summary>Executable SSpec</summary>

Runnable source: 75 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject unsupported unreadable and duplicate datapath drivers")
step("Reject unsupported operations, unreadable values, and multiple drivers")
val unsupported = rebuilt_mixed_module([
    HwCombOp.binary("unsupported", "sum", "lhs", "rhs", 32),
    HwCombOp.unary("trunc", "low_byte", "sum", 8),
    HwCombOp.unary("sext", "signed_byte", "low_byte", 32)],
    [HwConstant.bits("zero32", 32, 0)])
expect(unsupported.diagnostic()).to_equal(
    "HWIR-E-SEQUENTIAL-DATAPATH-COMB: unsupported combinational operation")
expect(render_strict_sequential_hwir(unsupported,
    "hwir-mixed-sequential-v1").is_success()).to_equal(false)

val unreadable = rebuilt_mixed_module([
    HwCombOp.binary("add", "sum", "value", "rhs", 32),
    HwCombOp.unary("trunc", "low_byte", "sum", 8),
    HwCombOp.unary("sext", "signed_byte", "low_byte", 32)],
    [HwConstant.bits("zero32", 32, 0)])
expect(unreadable.diagnostic()).to_equal(
    "HWIR-E-SEQUENTIAL-DATAPATH-COMB: combinational operation requires typed readable operands and signal result")

val duplicate = rebuilt_mixed_module([
    HwCombOp.binary("add", "sum", "lhs", "rhs", 32),
    HwCombOp.unary("trunc", "low_byte", "sum", 8),
    HwCombOp.unary("sext", "signed_byte", "low_byte", 32),
    HwCombOp.binary("add", "sum", "lhs", "rhs", 32)],
    [HwConstant.bits("zero32", 32, 0)])
expect(duplicate.diagnostic()).to_equal(
    "HWIR-E-SEQUENTIAL-DATAPATH-DRIVER: datapath values require one driver")

val invalid_resize = rebuilt_mixed_module([
    HwCombOp.binary("add", "sum", "lhs", "rhs", 32),
    HwCombOp.unary("trunc", "low_byte", "sum_bit", 8),
    HwCombOp.unary("sext", "signed_byte", "low_byte", 32)],
    [HwConstant.bits("zero32", 32, 0)])
expect(invalid_resize.diagnostic()).to_equal(
    "HWIR-E-SEQUENTIAL-DATAPATH-COMB: combinational operation requires typed readable operands and signal result")

val invalid_destination = rebuilt_mixed_module([
    HwCombOp.binary("add", "value_reg", "lhs", "rhs", 32),
    HwCombOp.unary("trunc", "low_byte", "sum", 8),
    HwCombOp.unary("sext", "signed_byte", "low_byte", 32)],
    [HwConstant.bits("zero32", 32, 0)])
expect(invalid_destination.diagnostic()).to_equal(
    "HWIR-E-SEQUENTIAL-DATAPATH-COMB: combinational operation requires typed readable operands and signal result")

val base = mixed_module()
var injected_ports = base.ports
injected_ports[2] = HwPort(name: "capture", direction: "in); end entity; --",
    type_name: "Bits", bit_width: 1, clock_domain: "default")
expect(rebuilt_mixed_module_with_ports(injected_ports).diagnostic()).to_equal(
    "HWIR-E-SEQUENTIAL-MODULE-PORT: sequential ports require unique default-domain Bits values")

val colliding_plan = HwSequentialPlan(owner_id: base.plan.owner_id,
    registers: [HwStateRegister(name: "LHS", bit_width: 1,
            clock_domain: "default", reset_value: 0),
        base.plan.registers[1]], rules: base.plan.rules,
    outputs: base.plan.outputs, decoder_pins: base.plan.decoder_pins)
val colliding = HwSequentialModuleDef(node_id: base.node_id,
    entity_name: base.entity_name, config: base.config, origins: base.origins,
    ports: base.ports, datapath_signals: base.datapath_signals,
    datapath_constants: base.datapath_constants,
    datapath_bit_vector_constants: base.datapath_bit_vector_constants,
    datapath_comb_ops: base.datapath_comb_ops,
    datapath_compare_ops: base.datapath_compare_ops,
    datapath_select_ops: base.datapath_select_ops,
    datapath_bit_extract_ops: base.datapath_bit_extract_ops,
    datapath_fixed_slice_ops: base.datapath_fixed_slice_ops,
    plan: colliding_plan, child_entity: "", child_graph_sha256: "")
expect(colliding.diagnostic()).to_equal(
    "HWIR-E-SEQUENTIAL-DATAPATH-NAMESPACE: ports, registers, child outputs, signals, and constants must be distinct")

expect(render_strict_sequential_hwir(base,
    "unsafe\nend architecture").diagnostic).to_equal(
    "HWIR-E-SEQUENTIAL-ROUTE: strict sequential route must be an explicit safe label")
```

</details>

#### should commit the typed datapath into the structural hash and VHDL receipt

- should commit the typed datapath into the structural hash and VHDL receipt
- Change a datapath constant and compare structural and emitted graph receipts
   - Expected: baseline.structural_sha256() == changed.structural_sha256() is false
   - Expected: emitted.hwir_graph_sha256 equals `baseline.structural_sha256()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should commit the typed datapath into the structural hash and VHDL receipt")
step("Change a datapath constant and compare structural and emitted graph receipts")
val baseline = mixed_module()
val changed = rebuilt_mixed_module([
    HwCombOp.binary("add", "sum", "lhs", "rhs", 32),
    HwCombOp.unary("trunc", "low_byte", "sum", 8),
    HwCombOp.unary("sext", "signed_byte", "low_byte", 32)],
    [HwConstant.bits("zero32", 32, 1)])
expect(baseline.structural_sha256() == changed.structural_sha256()).to_equal(false)
val emitted = render_strict_sequential_hwir(baseline,
    "hwir-mixed-sequential-v1")
expect(emitted.hwir_graph_sha256).to_equal(baseline.structural_sha256())
expect(emitted.vhdl).to_contain("graph=" + baseline.structural_sha256())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering mixed sequential HWIR datapath and explicit LSU geometry.
- mixed sequential HWIR datapath and explicit LSU geometry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `ae3851c684583bc81db6c71b8787980c004b13d5c3806407f20db2904da44fb9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae3851c684583bc81db6c71b8787980c004b13d5c3806407f20db2904da44fb9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae3851c684583bc81db6c71b8787980c004b13d5c3806407f20db2904da44fb9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=75 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render typed add truncate sign extension compare and select before state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render typed add truncate sign extension compare and select before state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl:129:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate LSU bus and mask widths independently of core widths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should validate LSU bus and mask widths independently of core widths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl:140:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept an XLEN unsigned predicate with a one-bit result' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept an XLEN unsigned predicate with a one-bit result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl:153:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsupported unreadable and duplicate datapath drivers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl:231:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should commit the typed datapath into the structural hash and VHDL receipt' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
