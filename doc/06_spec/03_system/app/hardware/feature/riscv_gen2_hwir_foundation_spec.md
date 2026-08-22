# RISC-V Gen2 HWIR Foundation

> Verifies the riscv gen2 hwir foundation behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V Gen2 HWIR Foundation

Verifies the riscv gen2 hwir foundation behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the riscv gen2 hwir foundation behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### RISC-V Gen2 HWIR foundation

#### should expose the fixed-width critical compressed subset without a full-Zca claim

- Verify: should expose the fixed-width critical compressed subset without a full-Zca claim
- Classify representative legal and illegal parcels through the text-free hardware boundary
   - Expected: ebreak.original_parcel equals `0x9002`
   - Expected: ebreak.canonical_instruction equals `0x00100073`
   - Expected: ebreak.length_bytes equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: ebreak.legal is true
   - Expected: ebreak.reason_code equals `COMPRESSED_REASON_NONE`
   - Expected: illegal.original_parcel equals `0x0000`
   - Expected: illegal.canonical_instruction equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: illegal.legal is false
- Derive the non-advertising capability boundary from the declarative ISA table
   - Expected: riscv_zca_critical_subset_entry_count() equals `25)  # oracle: pinned constant asserted by this scenario`
   - Expected: riscv_zca_critical_subset_entries().len() equals `25)  # oracle: pinned constant asserted by this scenario`
   - Expected: manifest.verified_entry_count equals `25)  # oracle: pinned constant asserted by this scenario`
   - Expected: manifest.advertises_extension is false
   - Expected: manifest.legacy_fallback_allowed is false
   - Expected: manifest.target_rtl_equivalence_verified is false
   - Expected: manifest.is_release_claimable() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should expose the fixed-width critical compressed subset without a full-Zca claim")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Classify representative legal and illegal parcels through the text-free hardware boundary")
val ebreak = riscv_zca_mission_critical_expand_hardware(0x9002)
val illegal = riscv_zca_mission_critical_expand_hardware(0x0000)
expect(ebreak.original_parcel).to_equal(0x9002)
expect(ebreak.canonical_instruction).to_equal(0x00100073)
expect(ebreak.length_bytes).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(ebreak.legal).to_equal(true)
expect(ebreak.reason_code).to_equal(COMPRESSED_REASON_NONE)
expect(illegal.original_parcel).to_equal(0x0000)
expect(illegal.canonical_instruction).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(illegal.legal).to_equal(false)
step("Derive the non-advertising capability boundary from the declarative ISA table")
val manifest = CompressedCriticalSubsetManifest.mission_critical_common_zca_v1()
expect(riscv_zca_critical_subset_entry_count()).to_equal(25)  # oracle: pinned constant asserted by this scenario
expect(riscv_zca_critical_subset_entries().len()).to_equal(25)  # oracle: pinned constant asserted by this scenario
expect(manifest.verified_entry_count).to_equal(25)  # oracle: pinned constant asserted by this scenario
expect(manifest.advertises_extension).to_equal(false)
expect(manifest.legacy_fallback_allowed).to_equal(false)
expect(manifest.target_rtl_equivalence_verified).to_equal(false)
expect(manifest.is_release_claimable()).to_equal(false)
```

</details>

#### should emit an RV32 strict module

- Verify: should emit an RV32 strict module
   - Artifact capture: after_step
- Select an RV32 Gen2 hardware product
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: lower.is_success() is true
- Emit the typed HWIR module without the legacy route
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `std_logic_vector(31 downto 0)`
   - Expected: emitted.uses_legacy_fallback() is false
- Analyze strict HWIR VHDL with the VHDL-2008 target toolchain
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: strict_ghdl_available() is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_rv32.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_rv32.vhd") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit an RV32 strict module")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Select an RV32 Gen2 hardware product")
val lower = lower_strict_hwir_and_module(HwirLowerInput.hardware("system_and", 2, 1, 0, 0), CoreConfig.rv32())
expect(lower.is_success()).to_equal(true)
if val module = lower.module:
    step("Emit the typed HWIR module without the legacy route")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("std_logic_vector(31 downto 0)")).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    step("Analyze strict HWIR VHDL with the VHDL-2008 target toolchain")
    expect(strict_ghdl_available()).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_rv32.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_rv32.vhd")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject an invalid product deterministically

- Verify: should reject an invalid product deterministically
- Reject an invalid elaboration configuration before VHDL emission
   - Expected: lower.is_success() is false
   - Expected: lower.diagnostic equals `HWIR-E-XLEN: expected 32 or 64`
   - Expected: lower.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should reject an invalid product deterministically")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Reject an invalid elaboration configuration before VHDL emission")
val invalid = CoreConfig(xlen: 128, physical_address_bits: 0, register_count: 0,
    profile: "", isa_profile: "", compressed_decode_profile: "")
val lower = lower_strict_hwir_and_module(HwirLowerInput.hardware("invalid", 2, 1, 0, 0), invalid)
expect(lower.is_success()).to_equal(false)
expect(lower.diagnostic).to_equal("HWIR-E-XLEN: expected 32 or 64")
expect(lower.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should emit and analyze a typed 16-bit parcel mask graph

- Verify: should emit and analyze a typed 16-bit parcel mask graph
   - Artifact capture: after_step
- Construct a fixed-width parcel mask with no textual VHDL operand
   - Artifact capture: after_step
- Emit and analyze the typed mask graph as VHDL-2008
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `to_unsigned(65535, 32)`
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_mask.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_mask.vhd") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit and analyze a typed 16-bit parcel mask graph")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Construct a fixed-width parcel mask with no textual VHDL operand")
val summary = HwModule(name: "strict_parcel_mask", profile: "rv32-zca",
    port_count: 2, signal_count: 0, register_count: 0, memory_count: 0,
    comb_op_count: 1, clock_domain_count: 1, fallback_function: "",
    cost: HwCostModel.empty())
val module = HwModuleDef(summary: summary, config: CoreConfig.rv32_zca_integer(),
    node_id: HwNodeId.module_root("strict_parcel_mask"),
    origins: [HwOrigin(node_id: HwNodeId.child("strict_parcel_mask", "mask"), source_name: "strict_parcel_mask")],
    ports: [HwPort.input("parcel", "Bits", 32), HwPort.output("masked", "Bits", 32)],
    signals: [], constants: [HwConstant.bits("low_16_mask", 32, 65535)],
    comb_ops: [HwCombOp.binary("and", "masked", "parcel", "low_16_mask", 32)],
    compare_ops: [], select_ops: [],
    clock_domains: [HwClockDomain.default_domain()])
step("Emit and analyze the typed mask graph as VHDL-2008")
val emitted = render_strict_hwir_vhdl(module)
expect(emitted.is_success()).to_equal(true)
expect(emitted.vhdl.contains("to_unsigned(65535, 32)")).to_equal(true)
expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_mask.vhd", emitted.vhdl)).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_mask.vhd")).to_equal(true)
```

</details>

#### should emit and analyze a bounded typed parcel right shift graph

- Verify: should emit and analyze a bounded typed parcel right shift graph
   - Artifact capture: after_step
- Construct a fixed-width parcel shift with a typed shift amount
   - Artifact capture: after_step
- Emit and analyze the typed shift graph as VHDL-2008
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `shift_right(unsigned(parcel), to_integer(unsigned(shift_amount)))`
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_shift.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_shift.vhd") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit and analyze a bounded typed parcel right shift graph")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Construct a fixed-width parcel shift with a typed shift amount")
val summary = HwModule(name: "strict_parcel_shift", profile: "rv32-zca",
    port_count: 2, signal_count: 0, register_count: 0, memory_count: 0,
    comb_op_count: 1, clock_domain_count: 1, fallback_function: "",
    cost: HwCostModel.empty())
val module = HwModuleDef(summary: summary, config: CoreConfig.rv32_zca_integer(),
    node_id: HwNodeId.module_root("strict_parcel_shift"),
    origins: [HwOrigin(node_id: HwNodeId.child("strict_parcel_shift", "shift"), source_name: "strict_parcel_shift")],
    ports: [HwPort.input("parcel", "Bits", 32), HwPort.output("shifted", "Bits", 32)],
    signals: [], constants: [HwConstant.bits("shift_amount", 32, 13)],
    comb_ops: [HwCombOp.binary("shr", "shifted", "parcel", "shift_amount", 32)],
    compare_ops: [], select_ops: [],
    clock_domains: [HwClockDomain.default_domain()])
step("Emit and analyze the typed shift graph as VHDL-2008")
val emitted = render_strict_hwir_vhdl(module)
expect(emitted.is_success()).to_equal(true)
expect(emitted.vhdl.contains("shift_right(unsigned(parcel), to_integer(unsigned(shift_amount)))")).to_equal(true)
expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_shift.vhd", emitted.vhdl)).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_shift.vhd")).to_equal(true)
```

</details>

#### should emit and simulate a bounded typed parcel left shift graph

- Verify: should emit and simulate a bounded typed parcel left shift graph
   - Artifact capture: after_step
- Construct a fixed-width left shift for canonical instruction fields
   - Artifact capture: after_step
- Emit, analyze, and simulate a canonical-field shift as VHDL-2008
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `shift_left(unsigned(parcel), to_integer(unsigned(shift_amount)))`
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_left_shift.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_left_shift.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_left_shift_tb.vhd", parcel_left_shift_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_left_shift_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_parcel_left_shift_tb") is true
   - Expected: strict_ghdl_run("strict_parcel_left_shift_tb", "2ns") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit and simulate a bounded typed parcel left shift graph")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Construct a fixed-width left shift for canonical instruction fields")
val summary = HwModule(name: "strict_parcel_left_shift", profile: "rv32-zca-critical",
    port_count: 2, signal_count: 0, register_count: 0, memory_count: 0,
    comb_op_count: 1, clock_domain_count: 1, fallback_function: "",
    cost: HwCostModel.empty())
val module = HwModuleDef(summary: summary, config: CoreConfig.rv32_zca_mission_critical(),
    node_id: HwNodeId.module_root("strict_parcel_left_shift"),
    origins: [HwOrigin(node_id: HwNodeId.child("strict_parcel_left_shift", "shift"), source_name: "strict_parcel_left_shift")],
    ports: [HwPort.input("parcel", "Bits", 32), HwPort.output("shifted", "Bits", 32)],
    signals: [], constants: [HwConstant.bits("shift_amount", 32, 7)],
    comb_ops: [HwCombOp.binary("shl", "shifted", "parcel", "shift_amount", 32)],
    compare_ops: [], select_ops: [],
    clock_domains: [HwClockDomain.default_domain()])
step("Emit, analyze, and simulate a canonical-field shift as VHDL-2008")
val emitted = render_strict_hwir_vhdl(module)
expect(emitted.is_success()).to_equal(true)
expect(emitted.vhdl.contains("shift_left(unsigned(parcel), to_integer(unsigned(shift_amount)))")).to_equal(true)
expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_left_shift.vhd", emitted.vhdl)).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_left_shift.vhd")).to_equal(true)
expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_left_shift_tb.vhd", parcel_left_shift_testbench())).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_left_shift_tb.vhd")).to_equal(true)
expect(strict_ghdl_elaborate("strict_parcel_left_shift_tb")).to_equal(true)
expect(strict_ghdl_run("strict_parcel_left_shift_tb", "2ns")).to_equal(true)
```

</details>

#### should emit and analyze a two-stage typed parcel field graph

- Verify: should emit and analyze a two-stage typed parcel field graph
   - Artifact capture: after_step
- Construct shift then mask through one typed internal signal
   - Artifact capture: after_step
- Emit and analyze the typed two-stage graph as VHDL-2008
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `signal shifted : std_logic_vector(31 downto 0);`
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_field.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_field.vhd") is true
- Simulate a known parcel through the generated field datapath
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_field_tb.vhd", parcel_field_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_field_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_parcel_field_tb") is true
   - Expected: strict_ghdl_run("strict_parcel_field_tb", "2ns") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit and analyze a two-stage typed parcel field graph")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Construct shift then mask through one typed internal signal")
val summary = HwModule(name: "strict_parcel_field", profile: "rv32-zca",
    port_count: 2, signal_count: 1, register_count: 0, memory_count: 0,
    comb_op_count: 2, clock_domain_count: 1, fallback_function: "",
    cost: HwCostModel.empty())
val module = HwModuleDef(summary: summary, config: CoreConfig.rv32_zca_integer(),
    node_id: HwNodeId.module_root("strict_parcel_field"),
    origins: [
        HwOrigin(node_id: HwNodeId.child("strict_parcel_field", "shift"), source_name: "strict_parcel_field"),
        HwOrigin(node_id: HwNodeId.child("strict_parcel_field", "mask"), source_name: "strict_parcel_field")
    ],
    ports: [HwPort.input("parcel", "Bits", 32), HwPort.output("field", "Bits", 32)],
    signals: [HwSignal(name: "shifted", type_name: "Bits", bit_width: 32, driver_count: 1, source_id: "strict_parcel_field")],
    constants: [HwConstant.bits("shift_amount", 32, 13), HwConstant.bits("field_mask", 32, 7)],
    comb_ops: [
        HwCombOp.binary("shr", "shifted", "parcel", "shift_amount", 32),
        HwCombOp.binary("and", "field", "shifted", "field_mask", 32)
    ],
    compare_ops: [], select_ops: [],
    clock_domains: [HwClockDomain.default_domain()])
step("Emit and analyze the typed two-stage graph as VHDL-2008")
val emitted = render_strict_hwir_vhdl(module)
expect(emitted.is_success()).to_equal(true)
expect(emitted.vhdl.contains("signal shifted : std_logic_vector(31 downto 0);")).to_equal(true)
expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_field.vhd", emitted.vhdl)).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_field.vhd")).to_equal(true)
step("Simulate a known parcel through the generated field datapath")
expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_parcel_field_tb.vhd", parcel_field_testbench())).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_parcel_field_tb.vhd")).to_equal(true)
expect(strict_ghdl_elaborate("strict_parcel_field_tb")).to_equal(true)
expect(strict_ghdl_run("strict_parcel_field_tb", "2ns")).to_equal(true)
```

</details>

#### should emit and simulate a typed C.EBREAK canonical leaf

- Verify: should emit and simulate a typed C.EBREAK canonical leaf
   - Artifact capture: after_step
- Construct the canonical EBREAK output as a typed u32 constant
   - Artifact capture: after_step
- Emit and simulate the canonical EBREAK leaf as VHDL-2008
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: emitted.is_success() is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cebreak_leaf.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cebreak_leaf.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cebreak_leaf_tb.vhd", cbreak_leaf_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cebreak_leaf_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cebreak_leaf_tb") is true
   - Expected: strict_ghdl_run("strict_cebreak_leaf_tb", "2ns") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit and simulate a typed C.EBREAK canonical leaf")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Construct the canonical EBREAK output as a typed u32 constant")
val summary = HwModule(name: "strict_cebreak_leaf", profile: "rv32-zca",
    port_count: 1, signal_count: 0, register_count: 0, memory_count: 0,
    comb_op_count: 1, clock_domain_count: 1, fallback_function: "",
    cost: HwCostModel.empty())
val module = HwModuleDef(summary: summary, config: CoreConfig.rv32_zca_integer(),
    node_id: HwNodeId.module_root("strict_cebreak_leaf"),
    origins: [HwOrigin(node_id: HwNodeId.child("strict_cebreak_leaf", "canonical"), source_name: "strict_cebreak_leaf")],
    ports: [HwPort.output("canonical_instruction", "Bits", 32)],
    signals: [], constants: [HwConstant.bits("canonical_value", 32, 1048691)],
    comb_ops: [HwCombOp.unary("passthrough", "canonical_instruction", "canonical_value", 32)],
    compare_ops: [], select_ops: [],
    clock_domains: [HwClockDomain.default_domain()])
step("Emit and simulate the canonical EBREAK leaf as VHDL-2008")
val emitted = render_strict_hwir_vhdl(module)
expect(emitted.is_success()).to_equal(true)
expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cebreak_leaf.vhd", emitted.vhdl)).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cebreak_leaf.vhd")).to_equal(true)
expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cebreak_leaf_tb.vhd", cbreak_leaf_testbench())).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cebreak_leaf_tb.vhd")).to_equal(true)
expect(strict_ghdl_elaborate("strict_cebreak_leaf_tb")).to_equal(true)
expect(strict_ghdl_run("strict_cebreak_leaf_tb", "2ns")).to_equal(true)
```

</details>

#### should emit and simulate a typed C.EBREAK predicate and canonical selection

- Verify: should emit and simulate a typed C.EBREAK predicate and canonical selection
   - Artifact capture: after_step
- Build the compiler-owned C.EBREAK row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.ebreak`
- Emit, analyze, and simulate both matched and unmatched parcel behavior
   - Artifact capture: after_step
   - Evidence: artifact verified by 9 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `when parcel = cbreak_parcel else '0'`
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cebreak_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cebreak_decode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cebreak_decode_tb.vhd", cbreak_decode_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cebreak_decode_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cebreak_decode_tb") is true
   - Expected: strict_ghdl_run("strict_cebreak_decode_tb", "3ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit and simulate a typed C.EBREAK predicate and canonical selection")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.EBREAK row for the concrete critical profile")
val built = strict_zca_cebreak_row_hwir("strict_cebreak_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.ebreak")
    step("Emit, analyze, and simulate both matched and unmatched parcel behavior")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("when parcel = cbreak_parcel else '0'")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cebreak_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cebreak_decode.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cebreak_decode_tb.vhd", cbreak_decode_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cebreak_decode_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cebreak_decode_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cebreak_decode_tb", "3ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the compiler-owned Zca C.ADDI4SPN row

- Verify: should exhaustively simulate the compiler-owned Zca C.ADDI4SPN row
   - Artifact capture: after_step
- Build the compiler-owned C.ADDI4SPN row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.addi4spn`
   - Expected: module.summary.comb_op_count equals `29)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_addi4spn_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_addi4spn_decode.vhd") is true
- Exhaustively simulate all 2,048 Q0/funct3=000 parcels including the reserved zero immediate
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_addi4spn_decode_exhaustive_tb.vhd", addi4spn_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_addi4spn_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_addi4spn_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_addi4spn_decode_exhaustive_tb", "2052ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the compiler-owned Zca C.ADDI4SPN row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.ADDI4SPN row for the concrete critical profile")
val built = strict_zca_addi4spn_row_hwir("strict_addi4spn_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.addi4spn")
    expect(module.summary.comb_op_count).to_equal(29)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_addi4spn_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_addi4spn_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 2,048 Q0/funct3=000 parcels including the reserved zero immediate")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_addi4spn_decode_exhaustive_tb.vhd", addi4spn_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_addi4spn_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_addi4spn_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_addi4spn_decode_exhaustive_tb", "2052ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the compiler-owned Zca C.LW row

- Verify: should exhaustively simulate the compiler-owned Zca C.LW row
   - Artifact capture: after_step
- Build the compiler-owned C.LW row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.lw`
   - Expected: module.summary.comb_op_count equals `28)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_lw_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_lw_decode.vhd") is true
- Exhaustively simulate all 2,048 Q0/funct3=010 C.LW parcels and a non-row parcel
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_lw_decode_exhaustive_tb.vhd", lw_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_lw_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_lw_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_lw_decode_exhaustive_tb", "2052ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the compiler-owned Zca C.LW row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.LW row for the concrete critical profile")
val built = strict_zca_lw_row_hwir("strict_lw_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.lw")
    expect(module.summary.comb_op_count).to_equal(28)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_lw_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_lw_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 2,048 Q0/funct3=010 C.LW parcels and a non-row parcel")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_lw_decode_exhaustive_tb.vhd", lw_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_lw_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_lw_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_lw_decode_exhaustive_tb", "2052ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the compiler-owned Zca C.SW row

- Verify: should exhaustively simulate the compiler-owned Zca C.SW row
   - Artifact capture: after_step
- Build the compiler-owned C.SW row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.sw`
   - Expected: module.summary.comb_op_count equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_sw_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_sw_decode.vhd") is true
- Exhaustively simulate all 2,048 Q0/funct3=110 C.SW parcels and a non-row parcel
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_sw_decode_exhaustive_tb.vhd", sw_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_sw_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_sw_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_sw_decode_exhaustive_tb", "2052ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the compiler-owned Zca C.SW row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.SW row for the concrete critical profile")
val built = strict_zca_sw_row_hwir("strict_sw_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.sw")
    expect(module.summary.comb_op_count).to_equal(32)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_sw_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_sw_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 2,048 Q0/funct3=110 C.SW parcels and a non-row parcel")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_sw_decode_exhaustive_tb.vhd", sw_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_sw_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_sw_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_sw_decode_exhaustive_tb", "2052ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the compiler-owned Zca C.LWSP row

- Verify: should exhaustively simulate the compiler-owned Zca C.LWSP row
   - Artifact capture: after_step
- Build the compiler-owned C.LWSP row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.lwsp`
   - Expected: module.summary.comb_op_count equals `26)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_lwsp_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_lwsp_decode.vhd") is true
- Exhaustively simulate all 4,096 Q2/funct3=010 C.LWSP parcels including reserved rd=x0
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_lwsp_decode_exhaustive_tb.vhd", lwsp_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_lwsp_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_lwsp_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_lwsp_decode_exhaustive_tb", "4100ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the compiler-owned Zca C.LWSP row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.LWSP row for the concrete critical profile")
val built = strict_zca_lwsp_row_hwir("strict_lwsp_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.lwsp")
    expect(module.summary.comb_op_count).to_equal(26)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_lwsp_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_lwsp_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 4,096 Q2/funct3=010 C.LWSP parcels including reserved rd=x0")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_lwsp_decode_exhaustive_tb.vhd", lwsp_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_lwsp_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_lwsp_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_lwsp_decode_exhaustive_tb", "4100ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the compiler-owned Zca C.SWSP row

- Verify: should exhaustively simulate the compiler-owned Zca C.SWSP row
   - Artifact capture: after_step
- Build the compiler-owned C.SWSP row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.swsp`
   - Expected: module.summary.comb_op_count equals `23)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_swsp_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_swsp_decode.vhd") is true
- Exhaustively simulate all 2,048 Q2/funct3=110 C.SWSP parcels and a non-row parcel
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_swsp_decode_exhaustive_tb.vhd", swsp_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_swsp_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_swsp_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_swsp_decode_exhaustive_tb", "2052ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the compiler-owned Zca C.SWSP row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.SWSP row for the concrete critical profile")
val built = strict_zca_swsp_row_hwir("strict_swsp_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.swsp")
    expect(module.summary.comb_op_count).to_equal(23)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_swsp_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_swsp_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 2,048 Q2/funct3=110 C.SWSP parcels and a non-row parcel")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_swsp_decode_exhaustive_tb.vhd", swsp_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_swsp_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_swsp_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_swsp_decode_exhaustive_tb", "2052ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the five-bit C.SLLI common row

- Verify: should exhaustively simulate the five-bit C.SLLI common row
   - Artifact capture: after_step
- Build the compiler-owned C.SLLI low-shamt row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.slli.low`
   - Expected: module.summary.comb_op_count equals `15)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_slli_low_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_slli_low_decode.vhd") is true
- Exhaustively simulate all 1,024 low-shamt parcels and reject the RV64-only high-shamt bit
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_slli_low_decode_exhaustive_tb.vhd", slli_low_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_slli_low_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_slli_low_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_slli_low_decode_exhaustive_tb", "1028ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the five-bit C.SLLI common row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.SLLI low-shamt row for the concrete critical profile")
val built = strict_zca_slli_low_row_hwir("strict_slli_low_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.slli.low")
    expect(module.summary.comb_op_count).to_equal(15)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_slli_low_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_slli_low_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 1,024 low-shamt parcels and reject the RV64-only high-shamt bit")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_slli_low_decode_exhaustive_tb.vhd", slli_low_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_slli_low_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_slli_low_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_slli_low_decode_exhaustive_tb", "1028ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the five-bit C.SRLI common row

- Verify: should exhaustively simulate the five-bit C.SRLI common row
   - Artifact capture: after_step
- Build the compiler-owned C.SRLI low-shamt row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.srli.low`
   - Expected: module.summary.comb_op_count equals `16)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_srli_low_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_srli_low_decode.vhd") is true
- Exhaustively simulate all 256 low-shamt C.SRLI parcels and reject C.SRAI and high-shamt forms
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_srli_low_decode_exhaustive_tb.vhd", srli_low_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_srli_low_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_srli_low_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_srli_low_decode_exhaustive_tb", "260ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the five-bit C.SRLI common row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.SRLI low-shamt row for the concrete critical profile")
val built = strict_zca_srli_low_row_hwir("strict_srli_low_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.srli.low")
    expect(module.summary.comb_op_count).to_equal(16)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_srli_low_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_srli_low_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 256 low-shamt C.SRLI parcels and reject C.SRAI and high-shamt forms")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_srli_low_decode_exhaustive_tb.vhd", srli_low_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_srli_low_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_srli_low_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_srli_low_decode_exhaustive_tb", "260ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the five-bit C.SRAI common row

- Verify: should exhaustively simulate the five-bit C.SRAI common row
   - Artifact capture: after_step
- Build the compiler-owned C.SRAI low-shamt row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.srai.low`
   - Expected: module.summary.comb_op_count equals `18)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_srai_low_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_srai_low_decode.vhd") is true
- Exhaustively simulate all 256 low-shamt C.SRAI parcels and reject C.SRLI and high-shamt forms
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_srai_low_decode_exhaustive_tb.vhd", srai_low_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_srai_low_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_srai_low_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_srai_low_decode_exhaustive_tb", "260ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the five-bit C.SRAI common row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.SRAI low-shamt row for the concrete critical profile")
val built = strict_zca_srai_low_row_hwir("strict_srai_low_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.srai.low")
    expect(module.summary.comb_op_count).to_equal(18)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_srai_low_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_srai_low_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 256 low-shamt C.SRAI parcels and reject C.SRLI and high-shamt forms")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_srai_low_decode_exhaustive_tb.vhd", srai_low_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_srai_low_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_srai_low_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_srai_low_decode_exhaustive_tb", "260ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the signed-immediate C.ANDI row

- Verify: should exhaustively simulate the signed-immediate C.ANDI row
   - Artifact capture: after_step
- Build the compiler-owned C.ANDI row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.andi`
   - Expected: module.summary.comb_op_count equals `22)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_candi_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_candi_decode.vhd") is true
- Exhaustively simulate all 512 C.ANDI parcels including both immediate-sign values
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_candi_decode_exhaustive_tb.vhd", candi_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_candi_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_candi_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_candi_decode_exhaustive_tb", "516ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the signed-immediate C.ANDI row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.ANDI row for the concrete critical profile")
val built = strict_zca_candi_row_hwir("strict_candi_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.andi")
    expect(module.summary.comb_op_count).to_equal(22)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_candi_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_candi_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 512 C.ANDI parcels including both immediate-sign values")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_candi_decode_exhaustive_tb.vhd", candi_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_candi_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_candi_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_candi_decode_exhaustive_tb", "516ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the compact-register C.SUB row

- Verify: should exhaustively simulate the compact-register C.SUB row
   - Artifact capture: after_step
- Build the compiler-owned C.SUB row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.sub`
   - Expected: module.summary.comb_op_count equals `18)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_csub_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_csub_decode.vhd") is true
- Exhaustively simulate all 64 compact C.SUB register pairs and reject C.XOR/C.SUBW
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_csub_decode_exhaustive_tb.vhd", csub_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_csub_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_csub_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_csub_decode_exhaustive_tb", "68ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the compact-register C.SUB row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.SUB row for the concrete critical profile")
val built = strict_zca_csub_row_hwir("strict_csub_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.sub")
    expect(module.summary.comb_op_count).to_equal(18)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_csub_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_csub_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 64 compact C.SUB register pairs and reject C.XOR/C.SUBW")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_csub_decode_exhaustive_tb.vhd", csub_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_csub_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_csub_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_csub_decode_exhaustive_tb", "68ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the compact-register C.XOR row

- Verify: should exhaustively simulate the compact-register C.XOR row
   - Artifact capture: after_step
- Build the compiler-owned C.XOR row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.xor`
   - Expected: module.summary.comb_op_count equals `18)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cxor_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cxor_decode.vhd") is true
- Exhaustively simulate all 64 compact C.XOR register pairs and reject adjacent modes
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cxor_decode_exhaustive_tb.vhd", cxor_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cxor_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cxor_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_cxor_decode_exhaustive_tb", "69ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the compact-register C.XOR row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.XOR row for the concrete critical profile")
val built = strict_zca_cxor_row_hwir("strict_cxor_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.xor")
    expect(module.summary.comb_op_count).to_equal(18)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cxor_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cxor_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 64 compact C.XOR register pairs and reject adjacent modes")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cxor_decode_exhaustive_tb.vhd", cxor_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cxor_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cxor_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cxor_decode_exhaustive_tb", "69ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the compact-register C.OR row

- Verify: should exhaustively simulate the compact-register C.OR row
   - Artifact capture: after_step
- Build the compiler-owned C.OR row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.or`
   - Expected: module.summary.comb_op_count equals `18)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cor_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cor_decode.vhd") is true
- Exhaustively simulate all 64 compact C.OR register pairs and reject adjacent modes
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cor_decode_exhaustive_tb.vhd", cor_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cor_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cor_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_cor_decode_exhaustive_tb", "69ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the compact-register C.OR row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.OR row for the concrete critical profile")
val built = strict_zca_cor_row_hwir("strict_cor_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.or")
    expect(module.summary.comb_op_count).to_equal(18)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cor_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cor_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 64 compact C.OR register pairs and reject adjacent modes")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cor_decode_exhaustive_tb.vhd", cor_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cor_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cor_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cor_decode_exhaustive_tb", "69ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the compact-register C.AND row

- Verify: should exhaustively simulate the compact-register C.AND row
   - Artifact capture: after_step
- Build the compiler-owned C.AND row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.and`
   - Expected: module.summary.comb_op_count equals `18)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cand_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cand_decode.vhd") is true
- Exhaustively simulate all 64 compact C.AND register pairs and reject adjacent modes
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cand_decode_exhaustive_tb.vhd", cand_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cand_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cand_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_cand_decode_exhaustive_tb", "69ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the compact-register C.AND row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.AND row for the concrete critical profile")
val built = strict_zca_cand_row_hwir("strict_cand_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.and")
    expect(module.summary.comb_op_count).to_equal(18)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cand_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cand_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all 64 compact C.AND register pairs and reject adjacent modes")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cand_decode_exhaustive_tb.vhd", cand_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cand_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cand_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cand_decode_exhaustive_tb", "69ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the C.JR row with reserved-register rejection

- Verify: should exhaustively simulate the C.JR row with reserved-register rejection
   - Artifact capture: after_step
- Build the compiler-owned C.JR row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.jr`
   - Expected: module.summary.comb_op_count equals `10)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjr_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjr_decode.vhd") is true
- Exhaustively simulate all C.JR register fields and reject reserved/adjacent forms
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjr_decode_exhaustive_tb.vhd", cjr_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjr_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cjr_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_cjr_decode_exhaustive_tb", "36ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the C.JR row with reserved-register rejection")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.JR row for the concrete critical profile")
val built = strict_zca_cjr_row_hwir("strict_cjr_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.jr")
    expect(module.summary.comb_op_count).to_equal(10)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjr_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjr_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all C.JR register fields and reject reserved/adjacent forms")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjr_decode_exhaustive_tb.vhd", cjr_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjr_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cjr_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cjr_decode_exhaustive_tb", "36ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the C.MV row with hint normalization

- Verify: should exhaustively simulate the C.MV row with hint normalization
   - Artifact capture: after_step
- Build the compiler-owned C.MV row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.mv`
   - Expected: module.summary.comb_op_count equals `16)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cmv_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cmv_decode.vhd") is true
- Exhaustively simulate all C.MV registers, the x0 hint, and neighboring forms
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cmv_decode_exhaustive_tb.vhd", cmv_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cmv_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cmv_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_cmv_decode_exhaustive_tb", "970ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the C.MV row with hint normalization")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.MV row for the concrete critical profile")
val built = strict_zca_cmv_row_hwir("strict_cmv_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.mv")
    expect(module.summary.comb_op_count).to_equal(16)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cmv_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cmv_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all C.MV registers, the x0 hint, and neighboring forms")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cmv_decode_exhaustive_tb.vhd", cmv_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cmv_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cmv_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cmv_decode_exhaustive_tb", "970ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the C.JALR row with reserved-register rejection

- Verify: should exhaustively simulate the C.JALR row with reserved-register rejection
   - Artifact capture: after_step
- Build the compiler-owned C.JALR row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.jalr`
   - Expected: module.summary.comb_op_count equals `11)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjalr_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjalr_decode.vhd") is true
- Exhaustively simulate all C.JALR registers and reject neighboring forms
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjalr_decode_exhaustive_tb.vhd", cjalr_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjalr_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cjalr_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_cjalr_decode_exhaustive_tb", "37ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the C.JALR row with reserved-register rejection")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.JALR row for the concrete critical profile")
val built = strict_zca_cjalr_row_hwir("strict_cjalr_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.jalr")
    expect(module.summary.comb_op_count).to_equal(11)  # oracle: pinned constant asserted by this scenario
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjalr_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjalr_decode.vhd")).to_equal(true)
    step("Exhaustively simulate all C.JALR registers and reject neighboring forms")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjalr_decode_exhaustive_tb.vhd", cjalr_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjalr_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cjalr_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cjalr_decode_exhaustive_tb", "37ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate C.ADD as separate RV32 and RV64 products

- Verify: should exhaustively simulate C.ADD as separate RV32 and RV64 products
   - Artifact capture: after_step
- Build concrete RV32 and RV64 C.ADD products without RTL XLEN selection
   - Artifact capture: after_step
   - Evidence: artifact verified by 22 expected checks
   - Expected: rv32.is_ok() is true
   - Expected: rv64.is_ok() is true
   - Expected: module32.shape_diagnostic() equals ``
   - Expected: module32.summary.comb_op_count equals `18)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted32.is_success() is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cadd_rv32_decode.vhd", emitted32.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cadd_rv32_decode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cadd_rv32_decode_exhaustive_tb.vhd", cadd_rv32_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cadd_rv32_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cadd_rv32_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_cadd_rv32_decode_exhaustive_tb", "995ns") is true
   - Expected: false is true
   - Expected: module64.shape_diagnostic() equals ``
   - Expected: module64.summary.comb_op_count equals `16)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted64.is_success() is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cadd_rv64_decode.vhd", emitted64.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cadd_rv64_decode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cadd_rv64_decode_exhaustive_tb.vhd", cadd_rv64_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cadd_rv64_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cadd_rv64_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_cadd_rv64_decode_exhaustive_tb", "995ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate C.ADD as separate RV32 and RV64 products")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build concrete RV32 and RV64 C.ADD products without RTL XLEN selection")
val rv32 = strict_zca_cadd_row_hwir("strict_cadd_rv32_decode", CoreConfig.rv32_zca_mission_critical())
val rv64 = strict_zca_cadd_row_hwir("strict_cadd_rv64_decode", CoreConfig.rv64_zca_mission_critical())
expect(rv32.is_ok()).to_equal(true)
expect(rv64.is_ok()).to_equal(true)
if val module32 = rv32.ok():
    expect(module32.shape_diagnostic()).to_equal("")
    expect(module32.summary.comb_op_count).to_equal(18)  # oracle: pinned constant asserted by this scenario
    val emitted32 = render_strict_hwir_vhdl(module32)
    expect(emitted32.is_success()).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cadd_rv32_decode.vhd", emitted32.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cadd_rv32_decode.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cadd_rv32_decode_exhaustive_tb.vhd", cadd_rv32_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cadd_rv32_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cadd_rv32_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cadd_rv32_decode_exhaustive_tb", "995ns")).to_equal(true)
else:
    expect(false).to_equal(true)
if val module64 = rv64.ok():
    expect(module64.shape_diagnostic()).to_equal("")
    expect(module64.summary.comb_op_count).to_equal(16)  # oracle: pinned constant asserted by this scenario
    val emitted64 = render_strict_hwir_vhdl(module64)
    expect(emitted64.is_success()).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cadd_rv64_decode.vhd", emitted64.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cadd_rv64_decode.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cadd_rv64_decode_exhaustive_tb.vhd", cadd_rv64_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cadd_rv64_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cadd_rv64_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cadd_rv64_decode_exhaustive_tb", "995ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should emit and simulate the shared Zca C.ADDI row as a typed critical graph

- Verify: should emit and simulate the shared Zca C.ADDI row as a typed critical graph
   - Artifact capture: after_step
- Build the compiler-owned C.ADDI/C.NOP row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.nop_addi`
   - Expected: module.summary.comb_op_count equals `20)  # oracle: pinned constant asserted by this scenario`
- Emit, analyze, and simulate both C.ADDI immediate signs and non-row rejection
   - Artifact capture: after_step
   - Evidence: artifact verified by 10 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: emitted.config_xlen equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: emitted.vhdl contains `shift_left(unsigned(imm12), to_integer(unsigned(left_shift_20)))`
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddi_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddi_decode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddi_decode_tb.vhd", caddi_decode_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddi_decode_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_caddi_decode_tb") is true
   - Expected: strict_ghdl_run("strict_caddi_decode_tb", "8ns") is true
- Exhaustively simulate all 2,048 C.ADDI/C.NOP parcel encodings
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddi_decode_exhaustive_tb.vhd", caddi_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddi_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_caddi_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_caddi_decode_exhaustive_tb", "2050ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit and simulate the shared Zca C.ADDI row as a typed critical graph")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.ADDI/C.NOP row for the concrete critical profile")
val built = strict_zca_caddi_row_hwir("strict_caddi_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.nop_addi")
    expect(module.summary.comb_op_count).to_equal(20)  # oracle: pinned constant asserted by this scenario
    step("Emit, analyze, and simulate both C.ADDI immediate signs and non-row rejection")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(emitted.config_xlen).to_equal(32)  # oracle: pinned constant asserted by this scenario
    expect(emitted.vhdl.contains("shift_left(unsigned(imm12), to_integer(unsigned(left_shift_20)))")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddi_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddi_decode.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddi_decode_tb.vhd", caddi_decode_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddi_decode_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_caddi_decode_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_caddi_decode_tb", "8ns")).to_equal(true)
    step("Exhaustively simulate all 2,048 C.ADDI/C.NOP parcel encodings")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddi_decode_exhaustive_tb.vhd", caddi_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddi_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_caddi_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_caddi_decode_exhaustive_tb", "2050ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the common Zca C.ADDI16SP row

- Verify: should exhaustively simulate the common Zca C.ADDI16SP row
   - Artifact capture: after_step
- Build the compiler-owned C.ADDI16SP row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.addi16sp`
   - Expected: module.summary.comb_op_count equals `36)  # oracle: pinned constant asserted by this scenario`
- Emit, analyze, and exhaustively simulate the 64 C.ADDI16SP immediate encodings
   - Artifact capture: after_step
   - Evidence: artifact verified by 9 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddi16sp_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddi16sp_decode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddi16sp_decode_exhaustive_tb.vhd", caddi16sp_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddi16sp_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_caddi16sp_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_caddi16sp_decode_exhaustive_tb", "68ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the common Zca C.ADDI16SP row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.ADDI16SP row for the concrete critical profile")
val built = strict_zca_caddi16sp_row_hwir("strict_caddi16sp_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.addi16sp")
    expect(module.summary.comb_op_count).to_equal(36)  # oracle: pinned constant asserted by this scenario
    step("Emit, analyze, and exhaustively simulate the 64 C.ADDI16SP immediate encodings")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddi16sp_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddi16sp_decode.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddi16sp_decode_exhaustive_tb.vhd", caddi16sp_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddi16sp_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_caddi16sp_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_caddi16sp_decode_exhaustive_tb", "68ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should exhaustively simulate the common Zca C.LUI row

- Verify: should exhaustively simulate the common Zca C.LUI row
   - Artifact capture: after_step
- Build the compiler-owned C.LUI row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.lui`
   - Expected: module.summary.comb_op_count equals `22)  # oracle: pinned constant asserted by this scenario`
- Emit, analyze, and exhaustively simulate the 2,048 C.LUI parcel encodings
   - Artifact capture: after_step
   - Evidence: artifact verified by 9 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_clui_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_clui_decode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_clui_decode_exhaustive_tb.vhd", clui_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_clui_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_clui_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_clui_decode_exhaustive_tb", "2052ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should exhaustively simulate the common Zca C.LUI row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.LUI row for the concrete critical profile")
val built = strict_zca_clui_row_hwir("strict_clui_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.lui")
    expect(module.summary.comb_op_count).to_equal(22)  # oracle: pinned constant asserted by this scenario
    step("Emit, analyze, and exhaustively simulate the 2,048 C.LUI parcel encodings")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_clui_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_clui_decode.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_clui_decode_exhaustive_tb.vhd", clui_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_clui_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_clui_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_clui_decode_exhaustive_tb", "2052ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should emit and exhaustively simulate the shared Zca C.LI row as a typed critical graph

- Verify: should emit and exhaustively simulate the shared Zca C.LI row as a typed critical graph
   - Artifact capture: after_step
- Build the compiler-owned C.LI row for the concrete critical profile
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.li`
   - Expected: module.summary.comb_op_count equals `18)  # oracle: pinned constant asserted by this scenario`
- Emit and exhaustively simulate all C.LI parcel encodings
   - Artifact capture: after_step
   - Evidence: artifact verified by 9 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cli_decode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cli_decode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cli_decode_exhaustive_tb.vhd", cli_exhaustive_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cli_decode_exhaustive_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cli_decode_exhaustive_tb") is true
   - Expected: strict_ghdl_run("strict_cli_decode_exhaustive_tb", "2052ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit and exhaustively simulate the shared Zca C.LI row as a typed critical graph")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the compiler-owned C.LI row for the concrete critical profile")
val built = strict_zca_cli_row_hwir("strict_cli_decode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.li")
    expect(module.summary.comb_op_count).to_equal(18)  # oracle: pinned constant asserted by this scenario
    step("Emit and exhaustively simulate all C.LI parcel encodings")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cli_decode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cli_decode.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cli_decode_exhaustive_tb.vhd", cli_exhaustive_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cli_decode_exhaustive_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cli_decode_exhaustive_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cli_decode_exhaustive_tb", "2052ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should render and simulate C.J predecode redirect semantics

- Verify: should render and simulate C.J predecode redirect semantics
   - Artifact capture: after_step
- Build C.J through the frozen typed predecode/redirect contract
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: built.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.port_width("original_parcel") equals `16)  # oracle: pinned constant asserted by this scenario`
   - Expected: module.port_width("fetch_pc") equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: module.port_width("redirect_target") equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: module.origins[3].source_name equals `zca.c.j`
- Emit, analyze, and simulate positive, negative, and non-row redirect behavior
   - Artifact capture: after_step
   - Evidence: artifact verified by 9 expected checks
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cj_predecode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cj_predecode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cj_predecode_tb.vhd", cj_predecode_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cj_predecode_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cj_predecode_tb") is true
   - Expected: strict_ghdl_run("strict_cj_predecode_tb", "4ns") is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-007 REQ-G2-008
step("Verify: should render and simulate C.J predecode redirect semantics")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build C.J through the frozen typed predecode/redirect contract")
val built = strict_zca_cj_predecode_row_hwir("strict_cj_predecode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.port_width("original_parcel")).to_equal(16)  # oracle: pinned constant asserted by this scenario
    expect(module.port_width("fetch_pc")).to_equal(32)  # oracle: pinned constant asserted by this scenario
    expect(module.port_width("redirect_target")).to_equal(32)  # oracle: pinned constant asserted by this scenario
    expect(module.origins[3].source_name).to_equal("zca.c.j")
    step("Emit, analyze, and simulate positive, negative, and non-row redirect behavior")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cj_predecode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cj_predecode.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cj_predecode_tb.vhd", cj_predecode_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cj_predecode_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cj_predecode_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cj_predecode_tb", "4ns")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should render RV32 C.JAL with x1 link semantics and reject the RV64 configuration

- Verify: should render RV32 C.JAL with x1 link semantics and reject the RV64 configuration
   - Artifact capture: after_step
- Build the RV32-only C.JAL row and reject its common-profile use
   - Artifact capture: after_step
   - Evidence: artifact verified by 19 expected checks
   - Expected: rv32.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.port_width("fetch_pc") equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: module.origins[2].source_name equals `zca.c.jal`
   - Expected: emitted.is_success() is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjal_rv32_predecode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjal_rv32_predecode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjal_rv32_predecode_tb.vhd", cjal_rv32_predecode_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjal_rv32_predecode_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cjal_rv32_predecode_tb") is true
   - Expected: strict_ghdl_run("strict_cjal_rv32_predecode_tb", "4ns") is true
   - Expected: false is true
   - Expected: common.is_err() is true
   - Expected: false is true
   - Expected: composed.is_ok() is true
   - Expected: composed_module.shape_diagnostic() equals ``
   - Expected: composed_module.origins.any(_.source_name == "zca.c.jal") is true
   - Expected: render_strict_hwir_vhdl(composed_module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should render RV32 C.JAL with x1 link semantics and reject the RV64 configuration")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the RV32-only C.JAL row and reject its common-profile use")
val rv32 = strict_zca_cjal_rv32_predecode_row_hwir("strict_cjal_rv32_predecode", CoreConfig.rv32_zca_cjal_mission_critical())
expect(rv32.is_ok()).to_equal(true)
if val module = rv32.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.port_width("fetch_pc")).to_equal(32)  # oracle: pinned constant asserted by this scenario
    expect(module.origins[2].source_name).to_equal("zca.c.jal")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjal_rv32_predecode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjal_rv32_predecode.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cjal_rv32_predecode_tb.vhd", cjal_rv32_predecode_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cjal_rv32_predecode_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_cjal_rv32_predecode_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_cjal_rv32_predecode_tb", "4ns")).to_equal(true)
else:
    expect(false).to_equal(true)
val common = strict_zca_cjal_rv32_predecode_row_hwir("strict_cjal_common_predecode", CoreConfig.rv32_zca_mission_critical())
expect(common.is_err()).to_equal(true)
if val diagnostic = common.err():
    expect(diagnostic).to_start_with("HWIR-E-ZCA-CJAL-PROFILE")
else:
    expect(false).to_equal(true)
val composed = strict_zca_rv32_cjal_migrating_predecode_hwir(
    "strict_cjal_rv32_composed", CoreConfig.rv32_zca_cjal_mission_critical())
expect(composed.is_ok()).to_equal(true)
if val composed_module = composed.ok():
    expect(composed_module.shape_diagnostic()).to_equal("")
    expect(composed_module.origins.any(_.source_name == "zca.c.jal")).to_equal(true)
    expect(render_strict_hwir_vhdl(composed_module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should render RV64 C.ADDIW only for its concrete profile and reject rd=x0

- Verify: should render RV64 C.ADDIW only for its concrete profile and reject rd=x0
   - Artifact capture: after_step
- Build the RV64-only C.ADDIW row and reject its common-profile use
   - Artifact capture: after_step
   - Evidence: artifact verified by 17 expected checks
   - Expected: rv64.is_ok() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.port_width("fetch_pc") equals `56)  # oracle: pinned constant asserted by this scenario`
   - Expected: module.origins[0].source_name equals `zca.c.addiw`
   - Expected: emitted.is_success() is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddiw_rv64_predecode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddiw_rv64_predecode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddiw_rv64_predecode_tb.vhd", caddiw_rv64_predecode_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddiw_rv64_predecode_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_caddiw_rv64_predecode_tb") is true
   - Expected: strict_ghdl_run("strict_caddiw_rv64_predecode_tb", "4ns") is true
   - Expected: false is true
   - Expected: composed.is_ok() is true
   - Expected: composed_module.shape_diagnostic() equals ``
   - Expected: composed_module.origins.any(_.source_name == "zca.c.addiw") is true
   - Expected: render_strict_hwir_vhdl(composed_module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should render RV64 C.ADDIW only for its concrete profile and reject rd=x0")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the RV64-only C.ADDIW row and reject its common-profile use")
val rv64 = strict_zca_caddiw_rv64_predecode_row_hwir("strict_caddiw_rv64_predecode",
    CoreConfig.rv64_zca_addiw_mission_critical())
expect(rv64.is_ok()).to_equal(true)
if val module = rv64.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.port_width("fetch_pc")).to_equal(56)  # oracle: pinned constant asserted by this scenario
    expect(module.origins[0].source_name).to_equal("zca.c.addiw")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddiw_rv64_predecode.vhd", emitted.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddiw_rv64_predecode.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_caddiw_rv64_predecode_tb.vhd", caddiw_rv64_predecode_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_caddiw_rv64_predecode_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_caddiw_rv64_predecode_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_caddiw_rv64_predecode_tb", "4ns")).to_equal(true)
else:
    expect(false).to_equal(true)
expect(strict_zca_caddiw_rv64_predecode_row_hwir("strict_caddiw_common",
    CoreConfig.rv64_zca_mission_critical()).is_err()).to_equal(true)
val composed = strict_zca_rv64_addiw_migrating_predecode_hwir(
    "strict_caddiw_rv64_composed", CoreConfig.rv64_zca_addiw_mission_critical())
expect(composed.is_ok()).to_equal(true)
if val composed_module = composed.ok():
    expect(composed_module.shape_diagnostic()).to_equal("")
    expect(composed_module.origins.any(_.source_name == "zca.c.addiw")).to_equal(true)
    expect(render_strict_hwir_vhdl(composed_module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should emit one fail-closed C.J/C.B control-predecode composition for RV32 and RV64

- Verify: should emit one fail-closed C.J/C.B control-predecode composition for RV32 and RV64
   - Artifact capture: after_step
- Compile the public strict Gen2 control-product entry point for both concrete XLENs
   - Artifact capture: after_step
   - Evidence: artifact verified by 12 expected checks
   - Expected: rv32.is_success() is true
   - Expected: rv64.is_success() is true
   - Expected: rv32.uses_legacy_fallback() is false
   - Expected: rv64.uses_legacy_fallback() is false
   - Expected: rv32.route equals `hwir-gen2-product`
   - Expected: rv64.route equals `hwir-gen2-product`
   - Expected: rv32.module_node_id equals `riscv_gen2_zca_control_predecode_rv32:module`
   - Expected: rv64.module_node_id equals `riscv_gen2_zca_control_predecode_rv64:module`
   - Expected: rv32.config_xlen equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: rv64.config_xlen equals `64)  # oracle: pinned constant asserted by this scenario`
   - Expected: rv32.config_profile equals `riscv-gen2-rv32-zca-critical`
   - Expected: rv64.config_profile equals `riscv-gen2-rv64-zca-critical`
- Run C.J, C.BEQZ, C.BNEZ, index-mismatch, and unsupported-parcel vectors in GHDL
   - Artifact capture: after_step
   - Evidence: artifact verified by 12 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_control_predecode_rv32.vhd", rv32.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_control_predecode_rv32.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_control_predecode_rv32_tb.vhd", control_predecode_testbench("riscv_gen2_zca_control_predecode_rv32", "strict_zca_control_predecode_rv32_tb", 32, 32, "x\"00000100\"", "x\"00000102\"")) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_control_predecode_rv32_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_zca_control_predecode_rv32_tb") is true
   - Expected: strict_ghdl_run("strict_zca_control_predecode_rv32_tb", "6ns") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_control_predecode_rv64.vhd", rv64.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_control_predecode_rv64.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_control_predecode_rv64_tb.vhd", control_predecode_testbench("riscv_gen2_zca_control_predecode_rv64", "strict_zca_control_predecode_rv64_tb", 56, 64, "x\"00000000000100\"", "x\"00000000000102\"")) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_control_predecode_rv64_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_zca_control_predecode_rv64_tb") is true
   - Expected: strict_ghdl_run("strict_zca_control_predecode_rv64_tb", "6ns") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit one fail-closed C.J/C.B control-predecode composition for RV32 and RV64")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Compile the public strict Gen2 control-product entry point for both concrete XLENs")
val rv32 = compile_strict_zca_control_predecode_product(CoreConfig.rv32_zca_mission_critical())
val rv64 = compile_strict_zca_control_predecode_product(CoreConfig.rv64_zca_mission_critical())
expect(rv32.is_success()).to_equal(true)
expect(rv64.is_success()).to_equal(true)
expect(rv32.uses_legacy_fallback()).to_equal(false)
expect(rv64.uses_legacy_fallback()).to_equal(false)
expect(rv32.route).to_equal("hwir-gen2-product")
expect(rv64.route).to_equal("hwir-gen2-product")
expect(rv32.module_node_id).to_equal("riscv_gen2_zca_control_predecode_rv32:module")
expect(rv64.module_node_id).to_equal("riscv_gen2_zca_control_predecode_rv64:module")
expect(rv32.config_xlen).to_equal(32)  # oracle: pinned constant asserted by this scenario
expect(rv64.config_xlen).to_equal(64)  # oracle: pinned constant asserted by this scenario
expect(rv32.config_profile).to_equal("riscv-gen2-rv32-zca-critical")
expect(rv64.config_profile).to_equal("riscv-gen2-rv64-zca-critical")
expect(rv32.vhdl).to_contain("route=hwir-gen2-product node=riscv_gen2_zca_control_predecode_rv32:module profile=riscv-gen2-rv32-zca-critical")
expect(rv64.vhdl).to_contain("route=hwir-gen2-product node=riscv_gen2_zca_control_predecode_rv64:module profile=riscv-gen2-rv64-zca-critical")
step("Run C.J, C.BEQZ, C.BNEZ, index-mismatch, and unsupported-parcel vectors in GHDL")
expect(strict_vhdl_write_file("/tmp/riscv_gen2_control_predecode_rv32.vhd", rv32.vhdl)).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_control_predecode_rv32.vhd")).to_equal(true)
expect(strict_vhdl_write_file("/tmp/riscv_gen2_control_predecode_rv32_tb.vhd", control_predecode_testbench("riscv_gen2_zca_control_predecode_rv32", "strict_zca_control_predecode_rv32_tb", 32, 32, "x\"00000100\"", "x\"00000102\""))).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_control_predecode_rv32_tb.vhd")).to_equal(true)
expect(strict_ghdl_elaborate("strict_zca_control_predecode_rv32_tb")).to_equal(true)
expect(strict_ghdl_run("strict_zca_control_predecode_rv32_tb", "6ns")).to_equal(true)
expect(strict_vhdl_write_file("/tmp/riscv_gen2_control_predecode_rv64.vhd", rv64.vhdl)).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_control_predecode_rv64.vhd")).to_equal(true)
expect(strict_vhdl_write_file("/tmp/riscv_gen2_control_predecode_rv64_tb.vhd", control_predecode_testbench("riscv_gen2_zca_control_predecode_rv64", "strict_zca_control_predecode_rv64_tb", 56, 64, "x\"00000000000100\"", "x\"00000000000102\""))).to_equal(true)
expect(strict_ghdl_analyze("/tmp/riscv_gen2_control_predecode_rv64_tb.vhd")).to_equal(true)
expect(strict_ghdl_elaborate("strict_zca_control_predecode_rv64_tb")).to_equal(true)
expect(strict_ghdl_run("strict_zca_control_predecode_rv64_tb", "6ns")).to_equal(true)
```

</details>

#### should render and simulate C.BEQZ/C.BNEZ operand-dependent redirect semantics for RV32

- Verify: should render and simulate C.BEQZ/C.BNEZ operand-dependent redirect semantics for RV32
   - Artifact capture: after_step
- Build both conditional rows through the frozen RV32 branch-predecode contract
   - Artifact capture: after_step
   - Evidence: artifact verified by 10 expected checks
   - Expected: beqz.is_ok() is true
   - Expected: bnez.is_ok() is true
   - Expected: beqz_module.shape_diagnostic() equals ``
   - Expected: bnez_module.shape_diagnostic() equals ``
   - Expected: beqz_module.port_width("rs1_index") equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: bnez_module.port_width("rs1_index") equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: beqz_module.port_width("rs1_value") equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: bnez_module.port_width("rs1_value") equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: beqz_module.origins[0].source_name equals `zca.c.beqz`
   - Expected: bnez_module.origins[0].source_name equals `zca.c.bnez`
- Emit, analyze, and simulate taken, untaken, negative-offset, and cross-row vectors
   - Artifact capture: after_step
   - Evidence: artifact verified by 14 expected checks
   - Expected: beqz_emitted.is_success() is true
   - Expected: bnez_emitted.is_success() is true
   - Expected: beqz_emitted.uses_legacy_fallback() is false
   - Expected: bnez_emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cbeqz_predecode_rv32.vhd", beqz_emitted.vhdl) is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cbnez_predecode_rv32.vhd", bnez_emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cbeqz_predecode_rv32.vhd") is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cbnez_predecode_rv32.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cb_predecode_rv32_tb.vhd", cb_index_binding_rv32_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cb_predecode_rv32_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cb_predecode_rv32_tb") is true
   - Expected: strict_ghdl_run("strict_cb_predecode_rv32_tb", "6ns") is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should render and simulate C.BEQZ/C.BNEZ operand-dependent redirect semantics for RV32")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build both conditional rows through the frozen RV32 branch-predecode contract")
val beqz = strict_zca_cbeqz_predecode_row_hwir("strict_cbeqz_predecode_rv32", CoreConfig.rv32_zca_mission_critical())
val bnez = strict_zca_cbnez_predecode_row_hwir("strict_cbnez_predecode_rv32", CoreConfig.rv32_zca_mission_critical())
expect(beqz.is_ok()).to_equal(true)
expect(bnez.is_ok()).to_equal(true)
if val beqz_module = beqz.ok():
    if val bnez_module = bnez.ok():
        expect(beqz_module.shape_diagnostic()).to_equal("")
        expect(bnez_module.shape_diagnostic()).to_equal("")
        expect(beqz_module.port_width("rs1_index")).to_equal(5)  # oracle: pinned constant asserted by this scenario
        expect(bnez_module.port_width("rs1_index")).to_equal(5)  # oracle: pinned constant asserted by this scenario
        expect(beqz_module.port_width("rs1_value")).to_equal(32)  # oracle: pinned constant asserted by this scenario
        expect(bnez_module.port_width("rs1_value")).to_equal(32)  # oracle: pinned constant asserted by this scenario
        expect(beqz_module.origins[0].source_name).to_equal("zca.c.beqz")
        expect(bnez_module.origins[0].source_name).to_equal("zca.c.bnez")
        step("Emit, analyze, and simulate taken, untaken, negative-offset, and cross-row vectors")
        val beqz_emitted = render_strict_hwir_vhdl(beqz_module)
        val bnez_emitted = render_strict_hwir_vhdl(bnez_module)
        expect(beqz_emitted.is_success()).to_equal(true)
        expect(bnez_emitted.is_success()).to_equal(true)
        expect(beqz_emitted.uses_legacy_fallback()).to_equal(false)
        expect(bnez_emitted.uses_legacy_fallback()).to_equal(false)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cbeqz_predecode_rv32.vhd", beqz_emitted.vhdl)).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cbnez_predecode_rv32.vhd", bnez_emitted.vhdl)).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cbeqz_predecode_rv32.vhd")).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cbnez_predecode_rv32.vhd")).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cb_predecode_rv32_tb.vhd", cb_index_binding_rv32_testbench())).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cb_predecode_rv32_tb.vhd")).to_equal(true)
        expect(strict_ghdl_elaborate("strict_cb_predecode_rv32_tb")).to_equal(true)
        expect(strict_ghdl_run("strict_cb_predecode_rv32_tb", "6ns")).to_equal(true)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should render and simulate C.BEQZ/C.BNEZ operand-dependent redirect semantics for RV64

- Verify: should render and simulate C.BEQZ/C.BNEZ operand-dependent redirect semantics for RV64
   - Artifact capture: after_step
- Build both conditional rows through the frozen RV64 branch-predecode contract
   - Artifact capture: after_step
   - Evidence: artifact verified by 12 expected checks
   - Expected: beqz.is_ok() is true
   - Expected: bnez.is_ok() is true
   - Expected: beqz_module.shape_diagnostic() equals ``
   - Expected: bnez_module.shape_diagnostic() equals ``
   - Expected: beqz_module.port_width("rs1_index") equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: bnez_module.port_width("rs1_index") equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: beqz_module.port_width("rs1_value") equals `64)  # oracle: pinned constant asserted by this scenario`
   - Expected: bnez_module.port_width("rs1_value") equals `64)  # oracle: pinned constant asserted by this scenario`
   - Expected: beqz_module.port_width("redirect_target") equals `56)  # oracle: pinned constant asserted by this scenario`
   - Expected: bnez_module.port_width("redirect_target") equals `56)  # oracle: pinned constant asserted by this scenario`
   - Expected: beqz_module.origins[0].source_name equals `zca.c.beqz`
   - Expected: bnez_module.origins[0].source_name equals `zca.c.bnez`
- Emit, analyze, and simulate XLEN-specialized branch vectors without runtime selection
   - Artifact capture: after_step
   - Evidence: artifact verified by 14 expected checks
   - Expected: beqz_emitted.is_success() is true
   - Expected: bnez_emitted.is_success() is true
   - Expected: beqz_emitted.uses_legacy_fallback() is false
   - Expected: bnez_emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cbeqz_predecode_rv64.vhd", beqz_emitted.vhdl) is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cbnez_predecode_rv64.vhd", bnez_emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cbeqz_predecode_rv64.vhd") is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cbnez_predecode_rv64.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cb_predecode_rv64_tb.vhd", cb_index_binding_rv64_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cb_predecode_rv64_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cb_predecode_rv64_tb") is true
   - Expected: strict_ghdl_run("strict_cb_predecode_rv64_tb", "6ns") is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should render and simulate C.BEQZ/C.BNEZ operand-dependent redirect semantics for RV64")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build both conditional rows through the frozen RV64 branch-predecode contract")
val beqz = strict_zca_cbeqz_predecode_row_hwir("strict_cbeqz_predecode_rv64", CoreConfig.rv64_zca_mission_critical())
val bnez = strict_zca_cbnez_predecode_row_hwir("strict_cbnez_predecode_rv64", CoreConfig.rv64_zca_mission_critical())
expect(beqz.is_ok()).to_equal(true)
expect(bnez.is_ok()).to_equal(true)
if val beqz_module = beqz.ok():
    if val bnez_module = bnez.ok():
        expect(beqz_module.shape_diagnostic()).to_equal("")
        expect(bnez_module.shape_diagnostic()).to_equal("")
        expect(beqz_module.port_width("rs1_index")).to_equal(5)  # oracle: pinned constant asserted by this scenario
        expect(bnez_module.port_width("rs1_index")).to_equal(5)  # oracle: pinned constant asserted by this scenario
        expect(beqz_module.port_width("rs1_value")).to_equal(64)  # oracle: pinned constant asserted by this scenario
        expect(bnez_module.port_width("rs1_value")).to_equal(64)  # oracle: pinned constant asserted by this scenario
        expect(beqz_module.port_width("redirect_target")).to_equal(56)  # oracle: pinned constant asserted by this scenario
        expect(bnez_module.port_width("redirect_target")).to_equal(56)  # oracle: pinned constant asserted by this scenario
        expect(beqz_module.origins[0].source_name).to_equal("zca.c.beqz")
        expect(bnez_module.origins[0].source_name).to_equal("zca.c.bnez")
        step("Emit, analyze, and simulate XLEN-specialized branch vectors without runtime selection")
        val beqz_emitted = render_strict_hwir_vhdl(beqz_module)
        val bnez_emitted = render_strict_hwir_vhdl(bnez_module)
        expect(beqz_emitted.is_success()).to_equal(true)
        expect(bnez_emitted.is_success()).to_equal(true)
        expect(beqz_emitted.uses_legacy_fallback()).to_equal(false)
        expect(bnez_emitted.uses_legacy_fallback()).to_equal(false)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cbeqz_predecode_rv64.vhd", beqz_emitted.vhdl)).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cbnez_predecode_rv64.vhd", bnez_emitted.vhdl)).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cbeqz_predecode_rv64.vhd")).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cbnez_predecode_rv64.vhd")).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_hwir_cb_predecode_rv64_tb.vhd", cb_index_binding_rv64_testbench())).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_hwir_cb_predecode_rv64_tb.vhd")).to_equal(true)
        expect(strict_ghdl_elaborate("strict_cb_predecode_rv64_tb")).to_equal(true)
        expect(strict_ghdl_run("strict_cb_predecode_rv64_tb", "6ns")).to_equal(true)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should route a critical hardware source through strict HWIR at the VHDL CLI boundary

- Verify: should route a critical hardware source through strict HWIR at the VHDL CLI boundary
   - Artifact capture: after_step
- Compile the critical source through the public VHDL CLI
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: strict_vhdl_write_file(source_path, "@hardware\nfn critical_and(a: bool, b: bool) -> bool:\n    a and b\n") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "critical") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: rt_file_exists(output_path) is true
   - Expected: rt_file_exists(manifest_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should route a critical hardware source through strict HWIR at the VHDL CLI boundary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Compile the critical source through the public VHDL CLI")
val source_path = "/tmp/riscv_gen2_critical_and.spl"
val output_path = "/tmp/riscv_gen2_critical_and.vhd"
val manifest_path = output_path + ".gen.json"
strict_remove_file_if_present(source_path)
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
expect(strict_vhdl_write_file(source_path, "@hardware\nfn critical_and(a: bool, b: bool) -> bool:\n    a and b\n")).to_equal(true)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "critical")).to_equal(true)
val (_stdout, _stderr, code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", source_path, "--riscv-gen2-target", "rv32", "--output", output_path])
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(rt_file_exists(output_path)).to_equal(true)
expect(rt_file_exists(manifest_path)).to_equal(true)
val vhdl = rt_file_read_text(output_path)
val manifest = rt_file_read_text(manifest_path)
expect(vhdl).to_contain("entity critical_and is")
expect(vhdl).to_contain("a and b")
expect(manifest).to_contain("\"name\":\"hwir-strict\"")
expect(manifest).to_contain("\"hwir_config_profile\":\"rv32\"")
strict_remove_file_if_present(source_path)
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
```

</details>

#### should derive a stateful frontend only from the fixed typed sequential plan

- Verify: should derive a stateful frontend only from the fixed typed sequential plan
   - Artifact capture: after_step
- Build concrete RV32 and RV64 stateful HWIR products
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: rv32.is_success() is true
   - Expected: rv64.is_success() is true
   - Expected: rv32.route equals `hwir-gen2-stateful-product-v2`
   - Expected: rv64.hwir_graph_sha256.len() equals `64)  # oracle: pinned constant asserted by this scenario`
   - Expected: rv32.uses_legacy_fallback() is false
   - Expected: rv64.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should derive a stateful frontend only from the fixed typed sequential plan")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build concrete RV32 and RV64 stateful HWIR products")
val rv32 = compile_strict_zca_single_outstanding_frontend_product(CoreConfig.rv32_zca_mission_critical())
val rv64 = compile_strict_zca_single_outstanding_frontend_product(CoreConfig.rv64_zca_mission_critical())
expect(rv32.is_success()).to_equal(true)
expect(rv64.is_success()).to_equal(true)
expect(rv32.route).to_equal("hwir-gen2-stateful-product-v2")
expect(rv64.hwir_graph_sha256.len()).to_equal(64)  # oracle: pinned constant asserted by this scenario
expect(rv32.vhdl).to_contain("graph=")
expect(rv32.vhdl).to_contain("elsif retire_valid='1' and valid_reg='1' and issued_reg='1' and retire_lineage=lineage_reg and retire_original_parcel=parcel_reg and retire_canonical_instruction=decoder_canonical and retire_original_length_bytes=decoder_length then")
expect(rv32.uses_legacy_fallback()).to_equal(false)
expect(rv64.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should bind the v2 C.EBREAK frontend to its typed state-graph closure

- Verify: should bind the v2 C.EBREAK frontend to its typed state-graph closure
   - Artifact capture: after_step
- Build the concrete RV32 trap frontend
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: rv32.is_success() is true
   - Expected: rv32.route equals `hwir-gen2-trap-stateful-product-v3`
   - Expected: rv32.hwir_graph_sha256.len() equals `64)  # oracle: pinned constant asserted by this scenario`
   - Expected: rv32.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should bind the v2 C.EBREAK frontend to its typed state-graph closure")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the concrete RV32 trap frontend")
val rv32 = compile_strict_zca_trap_single_outstanding_frontend_product(CoreConfig.rv32_zca_mission_critical())
expect(rv32.is_success()).to_equal(true)
expect(rv32.route).to_equal("hwir-gen2-trap-stateful-product-v3")
expect(rv32.hwir_graph_sha256.len()).to_equal(64)  # oracle: pinned constant asserted by this scenario
expect(rv32.vhdl).to_contain("trap_valid <= '1' when decoder_trap_valid='1' and valid_reg='1' and issued_reg='0' and fault_reg='0' else '0';")
expect(rv32.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should contain RV32 and RV64 stateful protocol faults in generated VHDL

- Verify: should contain RV32 and RV64 stateful protocol faults in generated VHDL
   - Artifact capture: after_step
- Build concrete RV32 and RV64 trap frontends
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: rv32.is_success() is true
   - Expected: rv64.is_success() is true
- Require the GHDL VHDL-2008 execution tool
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: strict_ghdl_available() is true
- Analyze, elaborate, and run the RV32 fault-containment and lineage-reuse vector
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_trap_stateful_rv32.vhd", rv32.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_trap_stateful_rv32.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_trap_stateful_rv32_tb.vhd", trap_stateful_reuse_reset_64_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv32", "strict_trap_stateful_protocol_rv32_tb", 32, 32, "x\"00000100\"")) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_trap_stateful_rv32_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_trap_stateful_protocol_rv32_tb") is true
   - Expected: strict_ghdl_run("strict_trap_stateful_protocol_rv32_tb", "220ns") is true
- Run three same-lineage RV32 retirement-identity mismatch vectors
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_trap_identity_rv32_tb.vhd", trap_stateful_identity_fault_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv32", "strict_trap_identity_rv32_tb", 32, 32, "x\"00000100\"")) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_trap_identity_rv32_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_trap_identity_rv32_tb") is true
   - Expected: strict_ghdl_run("strict_trap_identity_rv32_tb", "180ns") is true
- Analyze, elaborate, and run the RV64 fault-containment and lineage-reuse vector
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_trap_stateful_rv64.vhd", rv64.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_trap_stateful_rv64.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_trap_stateful_rv64_tb.vhd", trap_stateful_reuse_reset_64_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv64", "strict_trap_stateful_protocol_rv64_tb", 56, 64, "x\"00000000000100\"")) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_trap_stateful_rv64_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_trap_stateful_protocol_rv64_tb") is true
   - Expected: strict_ghdl_run("strict_trap_stateful_protocol_rv64_tb", "220ns") is true
- Run three same-lineage RV64 retirement-identity mismatch vectors
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_trap_identity_rv64_tb.vhd", trap_stateful_identity_fault_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv64", "strict_trap_identity_rv64_tb", 56, 64, "x\"00000000000100\"")) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_trap_identity_rv64_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_trap_identity_rv64_tb") is true
   - Expected: strict_ghdl_run("strict_trap_identity_rv64_tb", "180ns") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should contain RV32 and RV64 stateful protocol faults in generated VHDL")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build concrete RV32 and RV64 trap frontends")
val rv32 = compile_strict_zca_trap_single_outstanding_frontend_product(CoreConfig.rv32_zca_mission_critical())
val rv64 = compile_strict_zca_trap_single_outstanding_frontend_product(CoreConfig.rv64_zca_mission_critical())
expect(rv32.is_success()).to_equal(true)
expect(rv64.is_success()).to_equal(true)
step("Require the GHDL VHDL-2008 execution tool")
expect(strict_ghdl_available()).to_equal(true)
if strict_ghdl_available():
    step("Analyze, elaborate, and run the RV32 fault-containment and lineage-reuse vector")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_trap_stateful_rv32.vhd", rv32.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_trap_stateful_rv32.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_trap_stateful_rv32_tb.vhd", trap_stateful_reuse_reset_64_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv32", "strict_trap_stateful_protocol_rv32_tb", 32, 32, "x\"00000100\""))).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_trap_stateful_rv32_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_trap_stateful_protocol_rv32_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_trap_stateful_protocol_rv32_tb", "220ns")).to_equal(true)
    step("Run three same-lineage RV32 retirement-identity mismatch vectors")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_trap_identity_rv32_tb.vhd", trap_stateful_identity_fault_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv32", "strict_trap_identity_rv32_tb", 32, 32, "x\"00000100\""))).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_trap_identity_rv32_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_trap_identity_rv32_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_trap_identity_rv32_tb", "180ns")).to_equal(true)
    step("Analyze, elaborate, and run the RV64 fault-containment and lineage-reuse vector")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_trap_stateful_rv64.vhd", rv64.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_trap_stateful_rv64.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_trap_stateful_rv64_tb.vhd", trap_stateful_reuse_reset_64_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv64", "strict_trap_stateful_protocol_rv64_tb", 56, 64, "x\"00000000000100\""))).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_trap_stateful_rv64_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_trap_stateful_protocol_rv64_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_trap_stateful_protocol_rv64_tb", "220ns")).to_equal(true)
    step("Run three same-lineage RV64 retirement-identity mismatch vectors")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_trap_identity_rv64_tb.vhd", trap_stateful_identity_fault_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv64", "strict_trap_identity_rv64_tb", 56, 64, "x\"00000000000100\""))).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_trap_identity_rv64_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_trap_identity_rv64_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_trap_identity_rv64_tb", "180ns")).to_equal(true)
```

</details>

#### should preserve reset, stall, retirement, and stale-effect containment

- Verify: should preserve reset, stall, retirement, and stale-effect containment
   - Artifact capture: after_step
- Build concrete RV32 and RV64 trap frontends
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: rv32.is_success() is true
   - Expected: rv64.is_success() is true
- Require the GHDL VHDL-2008 execution tool
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: strict_ghdl_available() is true
- Run the extended RV32 reset and stale-effect protocol vector
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_trap_extended_rv32.vhd", rv32.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_trap_extended_rv32.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_trap_extended_rv32_tb.vhd", trap_stateful_protocol_64_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv32", "strict_trap_extended_rv32_tb", 32, 32, "x\"00000100\"")) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_trap_extended_rv32_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_trap_extended_rv32_tb") is true
   - Expected: strict_ghdl_run("strict_trap_extended_rv32_tb", "220ns") is true
- Run the extended RV64 reset and stale-effect protocol vector
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_trap_extended_rv64.vhd", rv64.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_trap_extended_rv64.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_trap_extended_rv64_tb.vhd", trap_stateful_protocol_64_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv64", "strict_trap_extended_rv64_tb", 56, 64, "x\"00000000000100\"")) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_trap_extended_rv64_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_trap_extended_rv64_tb") is true
   - Expected: strict_ghdl_run("strict_trap_extended_rv64_tb", "220ns") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-007 REQ-G2-008
step("Verify: should preserve reset, stall, retirement, and stale-effect containment")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build concrete RV32 and RV64 trap frontends")
val rv32 = compile_strict_zca_trap_single_outstanding_frontend_product(CoreConfig.rv32_zca_mission_critical())
val rv64 = compile_strict_zca_trap_single_outstanding_frontend_product(CoreConfig.rv64_zca_mission_critical())
expect(rv32.is_success()).to_equal(true)
expect(rv64.is_success()).to_equal(true)
step("Require the GHDL VHDL-2008 execution tool")
expect(strict_ghdl_available()).to_equal(true)
if strict_ghdl_available():
    step("Run the extended RV32 reset and stale-effect protocol vector")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_trap_extended_rv32.vhd", rv32.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_trap_extended_rv32.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_trap_extended_rv32_tb.vhd", trap_stateful_protocol_64_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv32", "strict_trap_extended_rv32_tb", 32, 32, "x\"00000100\""))).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_trap_extended_rv32_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_trap_extended_rv32_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_trap_extended_rv32_tb", "220ns")).to_equal(true)
    step("Run the extended RV64 reset and stale-effect protocol vector")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_trap_extended_rv64.vhd", rv64.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_trap_extended_rv64.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_trap_extended_rv64_tb.vhd", trap_stateful_protocol_64_testbench("riscv_gen2_zca_trap_single_outstanding_frontend_rv64", "strict_trap_extended_rv64_tb", 56, 64, "x\"00000000000100\""))).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_trap_extended_rv64_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_trap_extended_rv64_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_trap_extended_rv64_tb", "220ns")).to_equal(true)
```

</details>

#### should normalize a non-control Zca row with explicit reserved-encoding legality

- Verify: should normalize a non-control Zca row with explicit reserved-encoding legality
   - Artifact capture: after_step
- Build the C.ADDI4SPN outcome row with explicit reserved-encoding legality
   - Artifact capture: after_step
   - Evidence: artifact verified by 9 expected checks
   - Expected: emitted.is_success() is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_addi4spn_outcome.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_addi4spn_outcome.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_addi4spn_outcome_tb.vhd", addi4spn_outcome_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_addi4spn_outcome_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_addi4spn_outcome_tb") is true
   - Expected: strict_ghdl_run("strict_addi4spn_outcome_tb", "10ns") is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-007 REQ-G2-008
step("Verify: should normalize a non-control Zca row with explicit reserved-encoding legality")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the C.ADDI4SPN outcome row with explicit reserved-encoding legality")
val outcome = strict_zca_addi4spn_outcome_hwir("strict_addi4spn_outcome", CoreConfig.rv32_zca_mission_critical())
if outcome.is_ok():
    val emitted = render_strict_hwir_vhdl(outcome.ok().unwrap())
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl).to_contain("legal_nonreserved")
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_addi4spn_outcome.vhd", emitted.vhdl)).to_equal(true)
    if strict_ghdl_available():
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_addi4spn_outcome.vhd")).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_addi4spn_outcome_tb.vhd", addi4spn_outcome_testbench())).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_addi4spn_outcome_tb.vhd")).to_equal(true)
        expect(strict_ghdl_elaborate("strict_addi4spn_outcome_tb")).to_equal(true)
        expect(strict_ghdl_run("strict_addi4spn_outcome_tb", "10ns")).to_equal(true)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should normalize classifier-complete C.LW and C.SW rows without canonical sentinels

- Verify: should normalize classifier-complete C.LW and C.SW rows without canonical sentinels
   - Artifact capture: after_step
- Build the separate C.LW and C.SW outcome rows
   - Artifact capture: after_step
   - Evidence: artifact verified by 18 expected checks
   - Expected: lw.is_ok() is true
   - Expected: sw.is_ok() is true
   - Expected: lw_vhdl.is_success() is true
   - Expected: sw_vhdl.is_success() is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_lw_outcome.vhd", lw_vhdl.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_lw_outcome.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_lw_outcome_tb.vhd", lw_outcome_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_lw_outcome_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_lw_outcome_tb") is true
   - Expected: strict_ghdl_run("strict_lw_outcome_tb", "10ns") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_sw_outcome.vhd", sw_vhdl.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_sw_outcome.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_sw_outcome_tb.vhd", sw_outcome_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_sw_outcome_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_sw_outcome_tb") is true
   - Expected: strict_ghdl_run("strict_sw_outcome_tb", "10ns") is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-007 REQ-G2-008
step("Verify: should normalize classifier-complete C.LW and C.SW rows without canonical sentinels")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the separate C.LW and C.SW outcome rows")
val lw = strict_zca_lw_outcome_hwir("strict_lw_outcome", CoreConfig.rv32_zca_mission_critical())
val sw = strict_zca_sw_outcome_hwir("strict_sw_outcome", CoreConfig.rv32_zca_mission_critical())
expect(lw.is_ok()).to_equal(true)
expect(sw.is_ok()).to_equal(true)
if lw.is_ok() and sw.is_ok():
    val lw_vhdl = render_strict_hwir_vhdl(lw.ok().unwrap())
    val sw_vhdl = render_strict_hwir_vhdl(sw.ok().unwrap())
    expect(lw_vhdl.is_success()).to_equal(true)
    expect(sw_vhdl.is_success()).to_equal(true)
    expect(lw_vhdl.vhdl).to_contain("lw_is_c_lw")
    expect(sw_vhdl.vhdl).to_contain("sw_is_c_sw")
    if strict_ghdl_available():
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_lw_outcome.vhd", lw_vhdl.vhdl)).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_lw_outcome.vhd")).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_lw_outcome_tb.vhd", lw_outcome_testbench())).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_lw_outcome_tb.vhd")).to_equal(true)
        expect(strict_ghdl_elaborate("strict_lw_outcome_tb")).to_equal(true)
        expect(strict_ghdl_run("strict_lw_outcome_tb", "10ns")).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_sw_outcome.vhd", sw_vhdl.vhdl)).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_sw_outcome.vhd")).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_sw_outcome_tb.vhd", sw_outcome_testbench())).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_sw_outcome_tb.vhd")).to_equal(true)
        expect(strict_ghdl_elaborate("strict_sw_outcome_tb")).to_equal(true)
        expect(strict_ghdl_run("strict_sw_outcome_tb", "10ns")).to_equal(true)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should derive C.LWSP legality from the explicit reserved-register predicate

- Verify: should derive C.LWSP legality from the explicit reserved-register predicate
   - Artifact capture: after_step
- Build the C.LWSP outcome row with its reserved-register predicate
   - Artifact capture: after_step
   - Evidence: artifact verified by 10 expected checks
   - Expected: lwsp.is_ok() is true
   - Expected: emitted.is_success() is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_lwsp_outcome.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_lwsp_outcome.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_lwsp_outcome_tb.vhd", lwsp_outcome_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_lwsp_outcome_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_lwsp_outcome_tb") is true
   - Expected: strict_ghdl_run("strict_lwsp_outcome_tb", "10ns") is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-007 REQ-G2-008
step("Verify: should derive C.LWSP legality from the explicit reserved-register predicate")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the C.LWSP outcome row with its reserved-register predicate")
val lwsp = strict_zca_lwsp_outcome_hwir("strict_lwsp_outcome", CoreConfig.rv32_zca_mission_critical())
expect(lwsp.is_ok()).to_equal(true)
if lwsp.is_ok():
    val emitted = render_strict_hwir_vhdl(lwsp.ok().unwrap())
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl).to_contain("lwsp_legal_after_reserved_0")
    if strict_ghdl_available():
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_lwsp_outcome.vhd", emitted.vhdl)).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_lwsp_outcome.vhd")).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_lwsp_outcome_tb.vhd", lwsp_outcome_testbench())).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_lwsp_outcome_tb.vhd")).to_equal(true)
        expect(strict_ghdl_elaborate("strict_lwsp_outcome_tb")).to_equal(true)
        expect(strict_ghdl_run("strict_lwsp_outcome_tb", "10ns")).to_equal(true)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should emit one migrating decoder that selects admitted rows and reject unmigrated rows

- Verify: should emit one migrating decoder that selects admitted rows and reject unmigrated rows
   - Artifact capture: after_step
- Build the bounded migrating decoder from admitted outcome rows
   - Artifact capture: after_step
   - Evidence: artifact verified by 19 expected checks
   - Expected: built.is_ok() is true
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_migrating_predecode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_migrating_predecode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_migrating_predecode_tb.vhd", migrating_predecode_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_migrating_predecode_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_migrating_predecode_tb") is true
   - Expected: strict_ghdl_run("strict_migrating_predecode_tb", "10ns") is true
   - Expected: false is true
   - Expected: false is true
   - Expected: built64.is_ok() is true
   - Expected: emitted64.is_success() is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_migrating_predecode_rv64.vhd", emitted64.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_migrating_predecode_rv64.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_migrating_predecode_rv64_tb.vhd", migrating_predecode_rv64_partition_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_migrating_predecode_rv64_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_migrating_predecode_rv64_tb") is true
   - Expected: strict_ghdl_run("strict_migrating_predecode_rv64_tb", "10ns") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-007 REQ-G2-008
step("Verify: should emit one migrating decoder that selects admitted rows and reject unmigrated rows")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the bounded migrating decoder from admitted outcome rows")
val built = strict_zca_migrating_predecode_hwir("strict_migrating_predecode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if built.is_ok():
    val emitted = render_strict_hwir_vhdl(built.ok().unwrap())
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(emitted.vhdl).to_contain("migrating_canonical_after_")
    if strict_ghdl_available():
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_migrating_predecode.vhd", emitted.vhdl)).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_migrating_predecode.vhd")).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_migrating_predecode_tb.vhd", migrating_predecode_testbench())).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_migrating_predecode_tb.vhd")).to_equal(true)
        expect(strict_ghdl_elaborate("strict_migrating_predecode_tb")).to_equal(true)
        expect(strict_ghdl_run("strict_migrating_predecode_tb", "10ns")).to_equal(true)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
val built64 = strict_zca_migrating_predecode_hwir(
    "strict_migrating_predecode_rv64", CoreConfig.rv64_zca_mission_critical())
expect(built64.is_ok()).to_equal(true)
if built64.is_ok() and strict_ghdl_available():
    val emitted64 = render_strict_hwir_vhdl(built64.ok().unwrap())
    expect(emitted64.is_success()).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_migrating_predecode_rv64.vhd", emitted64.vhdl)).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_migrating_predecode_rv64.vhd")).to_equal(true)
    expect(strict_vhdl_write_file("/tmp/riscv_gen2_migrating_predecode_rv64_tb.vhd", migrating_predecode_rv64_partition_testbench())).to_equal(true)
    expect(strict_ghdl_analyze("/tmp/riscv_gen2_migrating_predecode_rv64_tb.vhd")).to_equal(true)
    expect(strict_ghdl_elaborate("strict_migrating_predecode_rv64_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_migrating_predecode_rv64_tb", "10ns")).to_equal(true)
```

</details>

#### should emit and simulate C.EBREAK as a breakpoint effect through the versioned trap contract

- Verify: should emit and simulate C.EBREAK as a breakpoint effect through the versioned trap contract
   - Artifact capture: after_step
- Build the C.EBREAK trap predecode row through the versioned contract
   - Artifact capture: after_step
   - Evidence: artifact verified by 11 expected checks
   - Expected: built.is_ok() is true
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_cebreak_trap_predecode.vhd", emitted.vhdl) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_cebreak_trap_predecode.vhd") is true
   - Expected: strict_vhdl_write_file("/tmp/riscv_gen2_cebreak_trap_predecode_tb.vhd", cbreak_trap_predecode_testbench()) is true
   - Expected: strict_ghdl_analyze("/tmp/riscv_gen2_cebreak_trap_predecode_tb.vhd") is true
   - Expected: strict_ghdl_elaborate("strict_cebreak_trap_predecode_tb") is true
   - Expected: strict_ghdl_run("strict_cebreak_trap_predecode_tb", "4ns") is true
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit and simulate C.EBREAK as a breakpoint effect through the versioned trap contract")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the C.EBREAK trap predecode row through the versioned contract")
val built = strict_zca_cebreak_trap_predecode_hwir("strict_cebreak_trap_predecode", CoreConfig.rv32_zca_mission_critical())
expect(built.is_ok()).to_equal(true)
if built.is_ok():
    val emitted = render_strict_hwir_vhdl(built.ok().unwrap())
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.uses_legacy_fallback()).to_equal(false)
    expect(emitted.vhdl).to_contain("trap_valid")
    expect(emitted.vhdl).to_contain("breakpoint_cause")
    if strict_ghdl_available():
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_cebreak_trap_predecode.vhd", emitted.vhdl)).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_cebreak_trap_predecode.vhd")).to_equal(true)
        expect(strict_vhdl_write_file("/tmp/riscv_gen2_cebreak_trap_predecode_tb.vhd", cbreak_trap_predecode_testbench())).to_equal(true)
        expect(strict_ghdl_analyze("/tmp/riscv_gen2_cebreak_trap_predecode_tb.vhd")).to_equal(true)
        expect(strict_ghdl_elaborate("strict_cebreak_trap_predecode_tb")).to_equal(true)
        expect(strict_ghdl_run("strict_cebreak_trap_predecode_tb", "4ns")).to_equal(true)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a Gen2 target outside critical assurance without touching a prior artifact

- Verify: should reject a Gen2 target outside critical assurance without touching a prior artifact
   - Artifact capture: after_step
- Prepare a prior artifact and invoke the noncritical target route
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: strict_vhdl_write_file(source_path, "@hardware\nfn noncritical_target_and(a: bool, b: bool) -> bool:\n    a and b\n") is true
   - Expected: strict_vhdl_write_file(output_path, "qualified-stale-artifact") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: code == 0 is false
   - Expected: stderr contains `HWIR-E-CRITICAL-POLICY") or rt_file_read_text(output_path) == "qualified-stal... (full value in folded executable source)`
   - Expected: rt_file_exists(output_path) is true
   - Expected: rt_file_read_text(output_path) equals `qualified-stale-artifact`
   - Expected: rt_file_exists(manifest_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should reject a Gen2 target outside critical assurance without touching a prior artifact")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prepare a prior artifact and invoke the noncritical target route")
val source_path = "/tmp/riscv_gen2_noncritical_target.spl"
val output_path = "/tmp/riscv_gen2_noncritical_target.vhd"
val manifest_path = output_path + ".gen.json"
strict_remove_file_if_present(source_path)
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
expect(strict_vhdl_write_file(source_path, "@hardware\nfn noncritical_target_and(a: bool, b: bool) -> bool:\n    a and b\n")).to_equal(true)
expect(strict_vhdl_write_file(output_path, "qualified-stale-artifact")).to_equal(true)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
val (_stdout, stderr, code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", source_path, "--riscv-gen2-target", "rv32", "--output", output_path])
expect(code == 0).to_equal(false)
expect(stderr.contains("HWIR-E-CRITICAL-POLICY") or rt_file_read_text(output_path) == "qualified-stale-artifact").to_equal(true)
expect(rt_file_exists(output_path)).to_equal(true)
expect(rt_file_read_text(output_path)).to_equal("qualified-stale-artifact")
expect(rt_file_exists(manifest_path)).to_equal(false)
strict_remove_file_if_present(source_path)
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
```

</details>

#### should emit the compiler-owned critical migrating Zca product without a synthetic source closure

- Verify: should emit the compiler-owned critical migrating Zca product without a synthetic source closure
   - Artifact capture: after_step
- Emit the source-less RV32 migrating product under critical policy
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "critical") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: rt_file_exists(output_path) is true
   - Expected: rt_file_exists(manifest_path) is true
   - Expected: manifest does not contain `"graph_sha256":""`
   - Expected: strict_ghdl_analyze(output_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit the compiler-owned critical migrating Zca product without a synthetic source closure")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Emit the source-less RV32 migrating product under critical policy")
val output_path = "/tmp/riscv_gen2_zca_migrating_product_rv32.vhd"
val manifest_path = output_path + ".gen.json"
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "critical")).to_equal(true)
val (_stdout, _stderr, code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", "--riscv-gen2-product", "riscv-gen2-zca-migrating-predecode-v1", "--riscv-gen2-target", "rv32-zca-critical", "--output", output_path])
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(rt_file_exists(output_path)).to_equal(true)
expect(rt_file_exists(manifest_path)).to_equal(true)
val vhdl = rt_file_read_text(output_path)
val manifest = rt_file_read_text(manifest_path)
expect(vhdl).to_contain("entity riscv_gen2_zca_migrating_predecode_rv32 is")
expect(manifest).to_contain("\"name\":\"hwir-gen2-product\"")
expect(manifest).to_contain("\"entry_module\":\"compiler-product:riscv-gen2-zca-migrating-predecode-v1\"")
expect(manifest).to_contain("\"source_closure\":[]")
expect(manifest).to_contain("\"kind\":\"compiler_product_entity\"")
expect(manifest).to_contain("\"riscv\":{\"isa_profile\":\"rv32i\",\"compressed_decode_profile\":\"zca-common-critical\",\"target_evidence_complete\":false}")
expect(manifest.contains("\"graph_sha256\":\"\"")).to_equal(false)
if strict_ghdl_available():
    expect(strict_ghdl_analyze(output_path)).to_equal(true)
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
```

</details>

#### should emit the typed-state v3 trap frontend with a nonempty closure hash

- Verify: should emit the typed-state v3 trap frontend with a nonempty closure hash
   - Artifact capture: after_step
- Emit the source-less RV64 typed-state trap frontend under critical policy
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "critical") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: rt_file_exists(output_path) is true
   - Expected: rt_file_exists(manifest_path) is true
   - Expected: manifest does not contain `"graph_sha256":""`
   - Expected: strict_ghdl_analyze(output_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit the typed-state v3 trap frontend with a nonempty closure hash")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Emit the source-less RV64 typed-state trap frontend under critical policy")
val output_path = "/tmp/riscv_gen2_zca_trap_frontend_rv64.vhd"
val manifest_path = output_path + ".gen.json"
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "critical")).to_equal(true)
val (_stdout, _stderr, code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", "--riscv-gen2-product", "riscv-gen2-zca-trap-single-outstanding-v3", "--riscv-gen2-target", "rv64-zca-critical", "--output", output_path])
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(rt_file_exists(output_path)).to_equal(true)
expect(rt_file_exists(manifest_path)).to_equal(true)
val vhdl = rt_file_read_text(output_path)
val manifest = rt_file_read_text(manifest_path)
expect(vhdl).to_contain("entity riscv_gen2_zca_trap_single_outstanding_frontend_rv64 is")
expect(vhdl).to_contain("graph=")
expect(manifest).to_contain("\"name\":\"hwir-gen2-trap-stateful-product-v3\"")
expect(manifest).to_contain("\"riscv\":{\"isa_profile\":\"rv64i\",\"compressed_decode_profile\":\"zca-common-critical\",\"target_evidence_complete\":false}")
expect(manifest.contains("\"graph_sha256\":\"\"")).to_equal(false)
if strict_ghdl_available():
    expect(strict_ghdl_analyze(output_path)).to_equal(true)
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
```

</details>

#### should emit source-less RV32 C.JAL trap v3 artifacts with the closed target admission manifest

- Verify: should emit source-less RV32 C.JAL trap v3 artifacts with the closed target admission manifest
   - Artifact capture: after_step
- Emit the specialized RV32 C.JAL trap product under its only admitted critical target
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "critical") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: rt_file_exists(output_path) is true
   - Expected: rt_file_exists(manifest_path) is true
   - Expected: manifest.split("\"zca.c.").len() equals `27)  # oracle: pinned constant asserted by this scenario`
   - Expected: manifest does not contain `"zca.c.addiw"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should emit source-less RV32 C.JAL trap v3 artifacts with the closed target admission manifest")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Emit the specialized RV32 C.JAL trap product under its only admitted critical target")
val output_path = "/tmp/riscv_gen2_zca_rv32_cjal_trap_frontend.vhd"
val manifest_path = output_path + ".gen.json"
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "critical")).to_equal(true)
val (_stdout, _stderr, code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", "--riscv-gen2-product", "riscv-gen2-zca-trap-single-outstanding-v3", "--riscv-gen2-target", "rv32-zca-cjal-critical", "--output", output_path])
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(rt_file_exists(output_path)).to_equal(true)
expect(rt_file_exists(manifest_path)).to_equal(true)
val vhdl = rt_file_read_text(output_path)
val manifest = rt_file_read_text(manifest_path)
expect(vhdl).to_contain("entity riscv_gen2_zca_rv32_cjal_trap_single_outstanding_frontend is")
expect(vhdl).to_contain("profile=riscv-gen2-rv32-zca-cjal-critical")
expect(manifest).to_contain("\"name\":\"hwir-gen2-trap-stateful-product-v3\"")
expect(manifest).to_contain("\"entry_module\":\"compiler-product:riscv-gen2-zca-trap-single-outstanding-v3\"")
expect(manifest).to_contain("\"source_closure\":[]")
expect(manifest).to_contain("\"target\":\"riscv32\"")
expect(manifest).to_contain("\"profile\":\"riscv-gen2-rv32-zca-cjal-critical\"")
expect(manifest).to_contain("\"kind\":\"compiler_product_dependency\",\"name\":\"riscv_gen2_zca_rv32_cjal_trap_migrating_predecode\"")
expect(manifest.split("\"zca.c.").len()).to_equal(27)  # oracle: pinned constant asserted by this scenario
expect(manifest).to_contain("\"zca.c.jal\"")
expect(manifest.contains("\"zca.c.addiw\"")).to_equal(false)
expect(manifest).to_contain("\"target_evidence_complete\":false")
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
```

</details>

#### should emit source-less RV64 C.ADDIW trap v3 artifacts with the closed target admission manifest

- Verify: should emit source-less RV64 C.ADDIW trap v3 artifacts with the closed target admission manifest
   - Artifact capture: after_step
- Emit the specialized RV64 C.ADDIW trap product under its only admitted critical target
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "critical") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: rt_file_exists(output_path) is true
   - Expected: rt_file_exists(manifest_path) is true
   - Expected: manifest.split("\"zca.c.").len() equals `33)  # oracle: pinned constant asserted by this scenario`
   - Expected: manifest does not contain `"zca.c.jal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-007 REQ-G2-008
step("Verify: should emit source-less RV64 C.ADDIW trap v3 artifacts with the closed target admission manifest")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Emit the specialized RV64 C.ADDIW trap product under its only admitted critical target")
val output_path = "/tmp/riscv_gen2_zca_rv64_addiw_trap_frontend.vhd"
val manifest_path = output_path + ".gen.json"
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "critical")).to_equal(true)
val (_stdout, _stderr, code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", "--riscv-gen2-product", "riscv-gen2-zca-trap-single-outstanding-v3", "--riscv-gen2-target", "rv64-zca-addiw-critical", "--output", output_path])
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(rt_file_exists(output_path)).to_equal(true)
expect(rt_file_exists(manifest_path)).to_equal(true)
val vhdl = rt_file_read_text(output_path)
val manifest = rt_file_read_text(manifest_path)
expect(vhdl).to_contain("entity riscv_gen2_zca_rv64_addiw_trap_single_outstanding_frontend is")
expect(vhdl).to_contain("profile=riscv-gen2-rv64-zca-addiw-critical")
expect(manifest).to_contain("\"name\":\"hwir-gen2-trap-stateful-product-v3\"")
expect(manifest).to_contain("\"entry_module\":\"compiler-product:riscv-gen2-zca-trap-single-outstanding-v3\"")
expect(manifest).to_contain("\"source_closure\":[]")
expect(manifest).to_contain("\"target\":\"riscv64\"")
expect(manifest).to_contain("\"profile\":\"riscv-gen2-rv64-zca-addiw-critical\"")
expect(manifest).to_contain("\"kind\":\"compiler_product_dependency\",\"name\":\"riscv_gen2_zca_rv64_addiw_trap_migrating_predecode\"")
expect(manifest.split("\"zca.c.").len()).to_equal(33)  # oracle: pinned constant asserted by this scenario
expect(manifest).to_contain("\"zca.c.addiw\"")
expect(manifest).to_contain("\"zca.c.ld\"")
expect(manifest).to_contain("\"zca.c.sd\"")
expect(manifest).to_contain("\"zca.c.ldsp\"")
expect(manifest).to_contain("\"zca.c.sdsp\"")
expect(manifest).to_contain("\"zca.c.addw\"")
expect(manifest).to_contain("\"zca.c.subw\"")
expect(manifest.contains("\"zca.c.jal\"")).to_equal(false)
expect(manifest).to_contain("\"target_evidence_complete\":false")
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
```

</details>

#### should execute the exact RV64 32-row decoder vectors through GHDL when available

- Verify: should execute the exact RV64 32-row decoder vectors through GHDL when available
   - Exec capture: after_step
   - Evidence: execution result verified by 7 expected checks
   - Expected: product.is_success() is true
   - Expected: strict_vhdl_write_file(product_path, product.vhdl) is true
   - Expected: strict_vhdl_write_file(testbench_path, rv64_full_trap_decoder_testbench()) is true
   - Expected: strict_ghdl_analyze(product_path) is true
   - Expected: strict_ghdl_analyze(testbench_path) is true
   - Expected: strict_ghdl_elaborate("strict_rv64_full_trap_decoder_tb") is true
   - Expected: strict_ghdl_run("strict_rv64_full_trap_decoder_tb", "20ns") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should execute the exact RV64 32-row decoder vectors through GHDL when available")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val product = compile_strict_zca_trap_single_outstanding_frontend_product(
    CoreConfig.rv64_zca_addiw_mission_critical())
expect(product.is_success()).to_equal(true)
expect(product.vhdl).to_contain("global_overlap_after_31")
if strict_ghdl_available():
    val product_path = "/tmp/riscv_gen2_rv64_full_trap_product.vhd"
    val testbench_path = "/tmp/riscv_gen2_rv64_full_trap_decoder_tb.vhd"
    expect(strict_vhdl_write_file(product_path, product.vhdl)).to_equal(true)
    expect(strict_vhdl_write_file(testbench_path, rv64_full_trap_decoder_testbench())).to_equal(true)
    expect(strict_ghdl_analyze(product_path)).to_equal(true)
    expect(strict_ghdl_analyze(testbench_path)).to_equal(true)
    expect(strict_ghdl_elaborate("strict_rv64_full_trap_decoder_tb")).to_equal(true)
    expect(strict_ghdl_run("strict_rv64_full_trap_decoder_tb", "20ns")).to_equal(true)
    strict_remove_file_if_present(product_path)
    strict_remove_file_if_present(testbench_path)
```

</details>

#### should preserve stale artifacts when specialized trap v3 target admission or critical policy fails

- Verify: should preserve stale artifacts when specialized trap v3 target admission or critical policy fails
   - Artifact capture: after_step
- Reject a wrong concrete target before the RV32 C.JAL product can replace an artifact
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: strict_vhdl_write_file(wrong_target_output, "qualified-stale-artifact") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "critical") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: wrong_code == 0 is false
   - Expected: rt_file_read_text(wrong_target_output) equals `qualified-stale-artifact`
   - Expected: rt_file_exists(wrong_target_manifest) is false
- Reject a noncritical request before the RV64 C.ADDIW product can replace an artifact
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: strict_vhdl_write_file(noncritical_output, "qualified-stale-artifact") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: noncritical_code == 0 is false
   - Expected: rt_file_read_text(noncritical_output) equals `qualified-stale-artifact`
   - Expected: rt_file_exists(noncritical_manifest) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should preserve stale artifacts when specialized trap v3 target admission or critical policy fails")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Reject a wrong concrete target before the RV32 C.JAL product can replace an artifact")
val wrong_target_output = "/tmp/riscv_gen2_zca_rv32_cjal_wrong_target.vhd"
val wrong_target_manifest = wrong_target_output + ".gen.json"
strict_remove_file_if_present(wrong_target_output)
strict_remove_file_if_present(wrong_target_manifest)
expect(strict_vhdl_write_file(wrong_target_output, "qualified-stale-artifact")).to_equal(true)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "critical")).to_equal(true)
val (_wrong_stdout, _wrong_stderr, wrong_code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", "--riscv-gen2-product", "riscv-gen2-zca-trap-single-outstanding-v3", "--riscv-gen2-target", "rv32-zca-critical", "--output", wrong_target_output])
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
expect(wrong_code == 0).to_equal(false)
expect(rt_file_read_text(wrong_target_output)).to_equal("qualified-stale-artifact")
expect(rt_file_exists(wrong_target_manifest)).to_equal(false)
step("Reject a noncritical request before the RV64 C.ADDIW product can replace an artifact")
val noncritical_output = "/tmp/riscv_gen2_zca_rv64_addiw_noncritical.vhd"
val noncritical_manifest = noncritical_output + ".gen.json"
strict_remove_file_if_present(noncritical_output)
strict_remove_file_if_present(noncritical_manifest)
expect(strict_vhdl_write_file(noncritical_output, "qualified-stale-artifact")).to_equal(true)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
val (_noncritical_stdout, _noncritical_stderr, noncritical_code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", "--riscv-gen2-product", "riscv-gen2-zca-trap-single-outstanding-v3", "--riscv-gen2-target", "rv64-zca-addiw-critical", "--output", noncritical_output])
expect(noncritical_code == 0).to_equal(false)
expect(rt_file_read_text(noncritical_output)).to_equal("qualified-stale-artifact")
expect(rt_file_exists(noncritical_manifest)).to_equal(false)
strict_remove_file_if_present(wrong_target_output)
strict_remove_file_if_present(wrong_target_manifest)
strict_remove_file_if_present(noncritical_output)
strict_remove_file_if_present(noncritical_manifest)
```

</details>

#### should reject the retired trap product identity before replacing an artifact

- Verify: should reject the retired trap product identity before replacing an artifact
   - Exec capture: after_step
- Reject the pre-widening v2 trap product identity
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: strict_vhdl_write_file(output_path, "qualified-stale-artifact") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "critical") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: code == 0 is false
   - Expected: rt_file_read_text(output_path) equals `qualified-stale-artifact`
   - Expected: rt_file_exists(manifest_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should reject the retired trap product identity before replacing an artifact")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Reject the pre-widening v2 trap product identity")
val output_path = "/tmp/riscv_gen2_retired_trap_product.vhd"
val manifest_path = output_path + ".gen.json"
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
expect(strict_vhdl_write_file(output_path, "qualified-stale-artifact")).to_equal(true)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "critical")).to_equal(true)
val (_stdout, _stderr, code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", "--riscv-gen2-product", "riscv-gen2-zca-trap-single-outstanding-v2", "--riscv-gen2-target", "rv64-zca-critical", "--output", output_path])
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
expect(code == 0).to_equal(false)
expect(rt_file_read_text(output_path)).to_equal("qualified-stale-artifact")
expect(rt_file_exists(manifest_path)).to_equal(false)
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
```

</details>

#### should reject a noncritical compiler-owned product before replacing a prior artifact

- Verify: should reject a noncritical compiler-owned product before replacing a prior artifact
   - Artifact capture: after_step
- Preserve a prior artifact while requesting a compiler product without critical policy
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: strict_vhdl_write_file(output_path, "qualified-stale-artifact") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: code == 0 is false
   - Expected: stderr contains `HWIR-E-CRITICAL-POLICY") or rt_file_read_text(output_path) == "qualified-stal... (full value in folded executable source)`
   - Expected: rt_file_read_text(output_path) equals `qualified-stale-artifact`
   - Expected: rt_file_exists(manifest_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-004 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should reject a noncritical compiler-owned product before replacing a prior artifact")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Preserve a prior artifact while requesting a compiler product without critical policy")
val output_path = "/tmp/riscv_gen2_zca_control_product_noncritical.vhd"
val manifest_path = output_path + ".gen.json"
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
expect(strict_vhdl_write_file(output_path, "qualified-stale-artifact")).to_equal(true)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
val (_stdout, stderr, code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", "--riscv-gen2-product", "riscv-gen2-zca-control-predecode-v1", "--riscv-gen2-target", "rv32-zca-critical", "--output", output_path])
expect(code == 0).to_equal(false)
expect(stderr.contains("HWIR-E-CRITICAL-POLICY") or rt_file_read_text(output_path) == "qualified-stale-artifact").to_equal(true)
expect(rt_file_read_text(output_path)).to_equal("qualified-stale-artifact")
expect(rt_file_exists(manifest_path)).to_equal(false)
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
```

</details>

#### should reject unsupported critical hardware before legacy VHDL artifacts exist

- Verify: should reject unsupported critical hardware before legacy VHDL artifacts exist
   - Artifact capture: after_step
- Compile unsupported critical hardware through the strict CLI boundary
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: strict_vhdl_write_file(source_path, "@hardware\nfn critical_xor(a: bool, b: bool) -> bool:\n    a xor b\n") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "critical") is true
   - Expected: rt_env_set("SIMPLE_SAFETY_PROFILE", "") is true
   - Expected: code == 0 is false
   - Expected: rt_file_exists(output_path) is false
   - Expected: rt_file_exists(manifest_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-G2-001 REQ-G2-002 REQ-G2-003 REQ-G2-004 REQ-G2-005 REQ-G2-006 REQ-G2-009 REQ-G2-010 REQ-G2-011 REQ-G2-007 REQ-G2-008
step("Verify: should reject unsupported critical hardware before legacy VHDL artifacts exist")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Compile unsupported critical hardware through the strict CLI boundary")
val source_path = "/tmp/riscv_gen2_critical_xor.spl"
val output_path = "/tmp/riscv_gen2_critical_xor.vhd"
val manifest_path = output_path + ".gen.json"
strict_remove_file_if_present(source_path)
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
expect(strict_vhdl_write_file(source_path, "@hardware\nfn critical_xor(a: bool, b: bool) -> bool:\n    a xor b\n")).to_equal(true)
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "critical")).to_equal(true)
val (_stdout, _stderr, code) = rt_process_run(qualification_simple_binary(), ["run", "src/app/cli/vhdl_compile_entry.spl", source_path, "--riscv-gen2-target", "rv32", "--output", output_path])
expect(rt_env_set("SIMPLE_SAFETY_PROFILE", "")).to_equal(true)
expect(code == 0).to_equal(false)
expect(rt_file_exists(output_path)).to_equal(false)
expect(rt_file_exists(manifest_path)).to_equal(false)
strict_remove_file_if_present(source_path)
strict_remove_file_if_present(output_path)
strict_remove_file_if_present(manifest_path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `99685187f25fd06b8aad8fed9f25f8ee251bd3970369c39041056bb2eb30e1d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99685187f25fd06b8aad8fed9f25f8ee251bd3970369c39041056bb2eb30e1d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99685187f25fd06b8aad8fed9f25f8ee251bd3970369c39041056bb2eb30e1d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl:239:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the fixed-width critical compressed subset without a full-Zca claim' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl:267:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit an RV32 strict module' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl:288:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an invalid product deterministically' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl:303:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit and analyze a typed 16-bit parcel mask graph' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl:330:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit and analyze a bounded typed parcel right shift graph' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl:357:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit and simulate a bounded typed parcel left shift graph' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
