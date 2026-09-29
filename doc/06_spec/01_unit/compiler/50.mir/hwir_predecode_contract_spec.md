# hwir_predecode_contract_spec

> Purpose: Prove that strict RISC-V compressed predecode contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_predecode_contract_spec

Purpose: Prove that strict RISC-V compressed predecode contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_predecode_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that strict RISC-V compressed predecode contract.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### strict RISC-V compressed predecode contract

#### REQ-G2-001 rejects duplicate strict-HWIR drivers before emission

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-G2-001 rejects duplicate strict-HWIR drivers before emission
- Verify: REQ-G2-001 rejects duplicate strict-HWIR drivers before emission
   - Expected: one_driver.shape_diagnostic() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-001 rejects duplicate strict-HWIR drivers before emission")
step("Verify: REQ-G2-001 rejects duplicate strict-HWIR drivers before emission")
val config = CoreConfig.rv32_zca_mission_critical()
val one_driver = HwModuleDef(
    summary: HwModule(name: "one_driver", profile: config.profile,
        port_count: 1, signal_count: 0, register_count: 0, memory_count: 0,
        comb_op_count: 1, clock_domain_count: 1, fallback_function: "",
        cost: HwCostModel.empty()), config: config,
    node_id: HwNodeId.module_root("one_driver"),
    origins: [HwOrigin(node_id: HwNodeId.child("one_driver", "source"), source_name: "test.one_driver")],
    ports: [HwPort.output("result", "Bits", 1)], signals: [],
    constants: [HwConstant.bits("zero", 1, 0)],
    comb_ops: [HwCombOp.unary("passthrough", "result", "zero", 1)],
    compare_ops: [], select_ops: [], clock_domains: [HwClockDomain.default_domain()])
expect(one_driver.shape_diagnostic()).to_equal("")
val duplicate_driver = HwModuleDef(
    summary: HwModule(name: "duplicate_driver", profile: config.profile,
        port_count: 1, signal_count: 0, register_count: 0, memory_count: 0,
        comb_op_count: 2, clock_domain_count: 1, fallback_function: "",
        cost: HwCostModel.empty()), config: config,
    node_id: HwNodeId.module_root("duplicate_driver"),
    origins: [HwOrigin(node_id: HwNodeId.child("duplicate_driver", "source"), source_name: "test.duplicate_driver")],
    ports: [HwPort.output("result", "Bits", 1)], signals: [],
    constants: [HwConstant.bits("zero", 1, 0)],
    comb_ops: [HwCombOp.unary("passthrough", "result", "zero", 1),
        HwCombOp.unary("passthrough", "result", "zero", 1)],
    compare_ops: [], select_ops: [], clock_domains: [HwClockDomain.default_domain()])
expect(duplicate_driver.shape_diagnostic()).to_start_with("HWIR-E-COMB")
```

</details>

#### REQ-G2-011 isolates RV32 C.JAL from the common profile and preserves its x1 link field

- REQ-G2-011 isolates RV32 C.JAL from the common profile and preserves its x1 link field
- Verify: REQ-G2-011 isolates RV32 C.JAL from the common profile and preserves its x1 link field
   - Expected: module.shape_diagnostic() equals ``
   - Expected: strict_origin_source_count(module, "zca.c.jal") equals `4`
   - Expected: link_field_present is true
   - Expected: false is true
   - Expected: common.is_err() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-011 isolates RV32 C.JAL from the common profile and preserves its x1 link field")
step("Verify: REQ-G2-011 isolates RV32 C.JAL from the common profile and preserves its x1 link field")
# @req: REQ-G2-001
val rv32 = strict_zca_cjal_rv32_predecode_row_hwir("cjal_rv32", CoreConfig.rv32_zca_cjal_mission_critical())
if val module = rv32.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(strict_origin_source_count(module, "zca.c.jal")).to_equal(4)
    var link_field_present = false
    for constant in module.constants:
        if constant.name == "jal_link_register_field" and constant.value == 128:
            link_field_present = true
    expect(link_field_present).to_equal(true)
else:
    expect(false).to_equal(true)
val common = strict_zca_cjal_rv32_predecode_row_hwir("cjal_common", CoreConfig.rv32_zca_mission_critical())
expect(common.is_err()).to_equal(true)
if val diagnostic = common.err():
    expect(diagnostic).to_start_with("HWIR-E-ZCA-CJAL-PROFILE")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-011 composes C.JAL only into a distinct RV32 migrating frontend product

- REQ-G2-011 composes C.JAL only into a distinct RV32 migrating frontend product
- Verify: REQ-G2-011 composes C.JAL only into a distinct RV32 migrating frontend product
   - Expected: decoded.shape_diagnostic() equals ``
   - Expected: decoded.ports.len() equals `10`
   - Expected: decoded.port_width("rs1_value") equals `32`
   - Expected: strict_zca_rv32_cjal_migrating_isa_ids() contains `zca.c.jal`
   - Expected: strict_output_driver_count(decoded, output_name) equals `1`
   - Expected: emitted.is_success() is true
   - Expected: emitted.config_profile equals `riscv-gen2-rv32-zca-cjal-critical`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-011 composes C.JAL only into a distinct RV32 migrating frontend product")
step("Verify: REQ-G2-011 composes C.JAL only into a distinct RV32 migrating frontend product")
val config = CoreConfig.rv32_zca_cjal_mission_critical()
val module = strict_zca_rv32_cjal_migrating_predecode_hwir(
    "rv32_cjal_migrating", config)
if val decoded = module.ok():
    expect(decoded.shape_diagnostic()).to_equal("")
    expect(decoded.ports.len()).to_equal(10)
    expect(decoded.port_width("rs1_value")).to_equal(32)
    expect(strict_origin_source_count(decoded, "zca.c.jal")).to_be_greater_than(0)
    expect(strict_zca_rv32_cjal_migrating_isa_ids().contains("zca.c.jal")).to_equal(true)
    for output_name in ["canonical_instruction", "original_length_bytes", "legal", "next_pc", "redirect_valid", "redirect_target"]:
        expect(strict_output_driver_count(decoded, output_name)).to_equal(1)
    val emitted = compile_strict_zca_rv32_cjal_migrating_predecode_product(config)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.config_profile).to_equal("riscv-gen2-rv32-zca-cjal-critical")
    expect(emitted.vhdl).to_contain("entity riscv_gen2_zca_rv32_cjal_migrating_predecode is")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-002/003 isolates RV64 C.ADDIW and fails an incompatible RV32 profile closed

- REQ-G2-002/003 isolates RV64 C.ADDIW and fails an incompatible RV32 profile closed
- Verify: REQ-G2-002/003 isolates RV64 C.ADDIW and fails an incompatible RV32 profile closed
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.port_width("fetch_pc") equals `56`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `entity caddiw_rv64 is`
   - Expected: false is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.port_width("rs1_value") equals `64`
   - Expected: strict_zca_rv64_addiw_migrating_isa_ids() contains `zca.c.addiw`
   - Expected: strict_output_driver_count(module, "canonical_instruction") equals `1`
   - Expected: compile_strict_zca_rv64_addiw_migrating_predecode_product(config).is_success() is true
   - Expected: false is true
   - Expected: rv32_rejected.is_err() is true
   - Expected: rv32_rejected.err().unwrap() equals `HWIR-E-ZCA-ADDIW-PROFILE: C.ADDIW requires the concrete RV64 Zca-ADDIW produc... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-002/003 isolates RV64 C.ADDIW and fails an incompatible RV32 profile closed")
step("Verify: REQ-G2-002/003 isolates RV64 C.ADDIW and fails an incompatible RV32 profile closed")
val config = CoreConfig.rv64_zca_addiw_mission_critical()
val row = strict_zca_caddiw_rv64_predecode_row_hwir("caddiw_rv64", config)
if val module = row.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.port_width("fetch_pc")).to_equal(56)
    expect(strict_origin_source_count(module, "zca.c.addiw")).to_be_greater_than(0)
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("entity caddiw_rv64 is")).to_equal(true)
else:
    expect(false).to_equal(true)
val frontend = strict_zca_rv64_addiw_migrating_predecode_hwir("caddiw_rv64_frontend", config)
if val module = frontend.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.port_width("rs1_value")).to_equal(64)
    expect(strict_origin_source_count(module, "zca.c.addiw")).to_be_greater_than(0)
    expect(strict_zca_rv64_addiw_migrating_isa_ids().contains("zca.c.addiw")).to_equal(true)
    expect(strict_output_driver_count(module, "canonical_instruction")).to_equal(1)
    expect(compile_strict_zca_rv64_addiw_migrating_predecode_product(config).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
val rv32_rejected = strict_zca_caddiw_rv64_predecode_row_hwir("caddiw_bad", CoreConfig.rv32_zca_cjal_mission_critical())
expect(rv32_rejected.is_err()).to_equal(true)
expect(rv32_rejected.err().unwrap()).to_equal("HWIR-E-ZCA-ADDIW-PROFILE: C.ADDIW requires the concrete RV64 Zca-ADDIW product profile")
expect(strict_zca_rv32_cjal_migrating_predecode_hwir(
    "rv64_cjal_rejected", CoreConfig.rv64_zca_mission_critical()).is_err()).to_equal(true)
```

</details>

#### REQ-G2-010 binds specialized parcel frontends to their exact elaborated decoders

- REQ-G2-010 binds specialized parcel frontends to their exact elaborated decoders
- Verify: REQ-G2-010 binds specialized parcel frontends to their exact elaborated decoders
   - Expected: cjal.ok().unwrap().decoder_entity equals `riscv_gen2_zca_rv32_cjal_migrating_predecode`
   - Expected: addiw.ok().unwrap().decoder_entity equals `riscv_gen2_zca_rv64_addiw_migrating_predecode`
   - Expected: emitted_cjal.is_success() is true
   - Expected: emitted_addiw.is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-010 binds specialized parcel frontends to their exact elaborated decoders")
step("Verify: REQ-G2-010 binds specialized parcel frontends to their exact elaborated decoders")
val cjal_config = CoreConfig.rv32_zca_cjal_mission_critical()
val addiw_config = CoreConfig.rv64_zca_addiw_mission_critical()
expect(strict_parcel_frontend_decoder_entity(cjal_config).unwrap()).to_equal(
    "riscv_gen2_zca_rv32_cjal_migrating_predecode")
expect(strict_parcel_frontend_decoder_entity(addiw_config).unwrap()).to_equal(
    "riscv_gen2_zca_rv64_addiw_migrating_predecode")
val cjal = strict_zca_single_outstanding_frontend_hwir(
    "riscv_gen2_zca_rv32_cjal_single_outstanding_frontend", cjal_config)
val addiw = strict_zca_single_outstanding_frontend_hwir(
    "riscv_gen2_zca_rv64_addiw_single_outstanding_frontend", addiw_config)
if cjal.is_ok() and addiw.is_ok():
    expect(cjal.ok().unwrap().decoder_entity).to_equal("riscv_gen2_zca_rv32_cjal_migrating_predecode")
    expect(addiw.ok().unwrap().decoder_entity).to_equal("riscv_gen2_zca_rv64_addiw_migrating_predecode")
    val emitted_cjal = compile_strict_zca_single_outstanding_frontend_product(cjal_config)
    val emitted_addiw = compile_strict_zca_single_outstanding_frontend_product(addiw_config)
    expect(emitted_cjal.is_success()).to_equal(true)
    expect(emitted_addiw.is_success()).to_equal(true)
    expect(emitted_cjal.vhdl).to_contain("entity riscv_gen2_zca_rv32_cjal_migrating_predecode is")
    expect(emitted_addiw.vhdl).to_contain("entity riscv_gen2_zca_rv64_addiw_migrating_predecode is")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-011 closes the v2 frontend admission list over the declarative critical subset

- REQ-G2-011 closes the v2 frontend admission list over the declarative critical subset
- Verify: REQ-G2-011 closes the v2 frontend admission list over the declarative critical subset
   - Expected: v1_ids.len() equals `expected.len() - 1`
   - Expected: v2_ids.len() equals `expected.len()`
   - Expected: v1_ids does not contain `zca.c.ebreak`
   - Expected: v2_ids contains `entry.id`
   - Expected: occurrences equals `1`
   - Expected: v2_match_count equals `v2_ids.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-011 closes the v2 frontend admission list over the declarative critical subset")
step("Verify: REQ-G2-011 closes the v2 frontend admission list over the declarative critical subset")
val expected = riscv_zca_critical_subset_entries()
val v1_ids = strict_zca_migrating_isa_ids()
val v2_ids = strict_zca_trap_migrating_isa_ids()
expect(v1_ids.len()).to_equal(expected.len() - 1)
expect(v2_ids.len()).to_equal(expected.len())
expect(v1_ids.contains("zca.c.ebreak")).to_equal(false)
var v2_match_count = 0
for entry in expected:
    expect(v2_ids.contains(entry.id)).to_equal(true)
    var occurrences = 0
    for id in v2_ids:
        if id == entry.id:
            occurrences = occurrences + 1
    expect(occurrences).to_equal(1)
    v2_match_count = v2_match_count + 1
expect(v2_match_count).to_equal(v2_ids.len())
```

</details>

#### REQ-G2-010 retains the v2 C.EBREAK trap effect through a one-entry frontend boundary

- REQ-G2-010 retains the v2 C.EBREAK trap effect through a one-entry frontend boundary
- Verify: REQ-G2-010 retains the v2 C.EBREAK trap effect through a one-entry frontend boundary
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.ports.len() equals `13`
   - Expected: strict_origin_source_count(module, "riscv.gen2.trap_migrating_predecode") equals `1`
   - Expected: strict_output_driver_count(module, "trap_valid") equals `1`
   - Expected: strict_output_driver_count(module, "trap_cause") equals `1`
   - Expected: strict_output_driver_count(module, "trap_tval") equals `1`
   - Expected: false is true
   - Expected: contract.shape_diagnostic() equals ``
   - Expected: contract.ports().len() equals `27`
   - Expected: contract.retire_original_parcel.name equals `retire_original_parcel`
   - Expected: contract.retire_canonical_instruction.name equals `retire_canonical_instruction`
   - Expected: contract.retire_original_length_bytes.name equals `retire_original_length_bytes`
   - Expected: contract.trap_valid.bit_width equals `1`
   - Expected: contract.trap_cause.bit_width equals `32`
   - Expected: false is true
   - Expected: product.shape_diagnostic() equals ``
   - Expected: product.decoder_entity equals `riscv_gen2_zca_trap_migrating_predecode_rv32`
   - Expected: product.registers.len() equals `8`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-010 retains the v2 C.EBREAK trap effect through a one-entry frontend boundary")
step("Verify: REQ-G2-010 retains the v2 C.EBREAK trap effect through a one-entry frontend boundary")
val config = CoreConfig.rv32_zca_mission_critical()
val decoder = strict_zca_trap_migrating_predecode_hwir("trap_migrating_predecode", config)
if val module = decoder.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.ports.len()).to_equal(13)
    expect(strict_origin_source_count(module, "riscv.gen2.trap_migrating_predecode")).to_equal(1)
    expect(strict_origin_source_count(module, "zca.c.ebreak.trap")).to_be_greater_than(0)
    expect(strict_output_driver_count(module, "trap_valid")).to_equal(1)
    expect(strict_output_driver_count(module, "trap_cause")).to_equal(1)
    expect(strict_output_driver_count(module, "trap_tval")).to_equal(1)
else:
    expect(false).to_equal(true)
val interface = strict_riscv_trap_parcel_frontend_interface(config)
if val contract = interface.ok():
    expect(contract.shape_diagnostic()).to_equal("")
    expect(contract.ports().len()).to_equal(27)
    expect(contract.retire_original_parcel.name).to_equal("retire_original_parcel")
    expect(contract.retire_canonical_instruction.name).to_equal("retire_canonical_instruction")
    expect(contract.retire_original_length_bytes.name).to_equal("retire_original_length_bytes")
    expect(contract.trap_valid.bit_width).to_equal(1)
    expect(contract.trap_cause.bit_width).to_equal(32)
else:
    expect(false).to_equal(true)
val frontend = strict_zca_trap_single_outstanding_frontend_hwir("trap_stateful_frontend", config)
if val product = frontend.ok():
    expect(product.shape_diagnostic()).to_equal("")
    expect(product.decoder_entity).to_equal("riscv_gen2_zca_trap_migrating_predecode_rv32")
    expect(product.registers.len()).to_equal(8)
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-003 rejects a malformed v2 trap-retirement interface

- REQ-G2-003 rejects a malformed v2 trap-retirement interface
- Verify: REQ-G2-003 rejects a malformed v2 trap-retirement interface
   - Expected: malformed.shape_diagnostic() equals `HWIR-E-TRAP-PARCEL-FRONTEND-OUTPUT-WIDTH: trap frontend output widths do not ... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-003 rejects a malformed v2 trap-retirement interface")
step("Verify: REQ-G2-003 rejects a malformed v2 trap-retirement interface")
val config = CoreConfig.rv32_zca_mission_critical()
val base = strict_riscv_trap_parcel_frontend_interface(config)
if val contract = base.ok():
    val malformed = HwTrapParcelFrontendInterface(
        node_id: contract.node_id, config: contract.config,
        clk: contract.clk, rst: contract.rst, fetch_valid: contract.fetch_valid,
        fetch_parcel: contract.fetch_parcel, fetch_pc: contract.fetch_pc,
        rs1_index: contract.rs1_index, rs1_value: contract.rs1_value,
        dispatch_accept: contract.dispatch_accept, retire_valid: contract.retire_valid,
        retire_lineage: contract.retire_lineage,
        retire_original_parcel: contract.retire_original_parcel,
        retire_canonical_instruction: contract.retire_canonical_instruction,
        retire_original_length_bytes: contract.retire_original_length_bytes,
        fetch_ready: contract.fetch_ready,
        dispatch_valid: contract.dispatch_valid, dispatch_lineage: contract.dispatch_lineage,
        protocol_fault: contract.protocol_fault, original_parcel: contract.original_parcel,
        canonical_instruction: contract.canonical_instruction,
        original_length_bytes: contract.original_length_bytes, legal: contract.legal,
        next_pc: contract.next_pc, redirect_valid: contract.redirect_valid,
        redirect_target: contract.redirect_target,
        trap_valid: HwPort.output("trap_valid", "Bits", 2),
        trap_cause: contract.trap_cause, trap_tval: contract.trap_tval
    )
    expect(malformed.shape_diagnostic()).to_equal("HWIR-E-TRAP-PARCEL-FRONTEND-OUTPUT-WIDTH: trap frontend output widths do not match its concrete product configuration")
else:
    expect(false).to_equal(true)
```

</details>

#### should close each specialized trap decoder over exactly one target row and C.EBREAK

- should close each specialized trap decoder over exactly one target row and C.EBREAK
- Build the RV32 C.JAL and RV64 C.ADDIW trap decoders from their concrete profiles
   - Expected: rv32_ids.is_ok() is true
   - Expected: rv64_ids.is_ok() is true
   - Expected: rv32_ids.ok().unwrap().len() equals `26`
   - Expected: rv64_ids.ok().unwrap().len() equals `32`
   - Expected: rv32_ids.ok().unwrap() contains `zca.c.jal`
   - Expected: rv32_ids.ok().unwrap() does not contain `zca.c.addiw`
   - Expected: rv64_ids.ok().unwrap() contains `zca.c.addiw`
   - Expected: rv64_ids.ok().unwrap() does not contain `zca.c.jal`
   - Expected: rv64_ids.ok().unwrap() contains `zca.c.ld`
   - Expected: rv64_ids.ok().unwrap() contains `zca.c.sd`
   - Expected: rv64_ids.ok().unwrap() contains `zca.c.ldsp`
   - Expected: rv64_ids.ok().unwrap() contains `zca.c.sdsp`
   - Expected: rv64_ids.ok().unwrap() contains `zca.c.addw`
   - Expected: rv64_ids.ok().unwrap() contains `zca.c.subw`
   - Expected: rv32_ebreak_count equals `1`
   - Expected: rv64_ebreak_count equals `1`
- Reject the generic profile before it can claim a target-specific trap closure
   - Expected: generic_rejected.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should close each specialized trap decoder over exactly one target row and C.EBREAK")
step("Build the RV32 C.JAL and RV64 C.ADDIW trap decoders from their concrete profiles")
val rv32_config = CoreConfig.rv32_zca_cjal_mission_critical()
val rv64_config = CoreConfig.rv64_zca_addiw_mission_critical()
val rv32_ids = strict_zca_target_trap_migrating_isa_ids(rv32_config)
val rv64_ids = strict_zca_target_trap_migrating_isa_ids(rv64_config)
expect(rv32_ids.is_ok()).to_equal(true)
expect(rv64_ids.is_ok()).to_equal(true)
expect(rv32_ids.ok().unwrap().len()).to_equal(26)
expect(rv64_ids.ok().unwrap().len()).to_equal(32)
expect(rv32_ids.ok().unwrap().contains("zca.c.jal")).to_equal(true)
expect(rv32_ids.ok().unwrap().contains("zca.c.addiw")).to_equal(false)
expect(rv64_ids.ok().unwrap().contains("zca.c.addiw")).to_equal(true)
expect(rv64_ids.ok().unwrap().contains("zca.c.jal")).to_equal(false)
expect(rv64_ids.ok().unwrap().contains("zca.c.ld")).to_equal(true)
expect(rv64_ids.ok().unwrap().contains("zca.c.sd")).to_equal(true)
expect(rv64_ids.ok().unwrap().contains("zca.c.ldsp")).to_equal(true)
expect(rv64_ids.ok().unwrap().contains("zca.c.sdsp")).to_equal(true)
expect(rv64_ids.ok().unwrap().contains("zca.c.addw")).to_equal(true)
expect(rv64_ids.ok().unwrap().contains("zca.c.subw")).to_equal(true)
var rv32_ebreak_count = 0
for id in rv32_ids.ok().unwrap():
    if id == "zca.c.ebreak":
        rv32_ebreak_count = rv32_ebreak_count + 1
var rv64_ebreak_count = 0
for id in rv64_ids.ok().unwrap():
    if id == "zca.c.ebreak":
        rv64_ebreak_count = rv64_ebreak_count + 1
expect(rv32_ebreak_count).to_equal(1)
expect(rv64_ebreak_count).to_equal(1)
step("Reject the generic profile before it can claim a target-specific trap closure")
val generic_rejected = strict_zca_target_trap_migrating_isa_ids(CoreConfig.rv32_zca_mission_critical())
expect(generic_rejected.is_err()).to_equal(true)
expect(generic_rejected.err().unwrap()).to_start_with("HWIR-E-ZCA-TARGET-TRAP-PROFILE")
```

</details>

#### should bind each specialized trap frontend and decoder to one closed no-overlap graph

- should bind each specialized trap frontend and decoder to one closed no-overlap graph
- Lower concrete RV32 C.JAL and RV64 C.ADDIW trap products with their selected decoder identities
   - Expected: rv32_decoder.is_ok() is true
   - Expected: rv64_decoder.is_ok() is true
   - Expected: rv32_frontend.is_ok() is true
   - Expected: rv64_frontend.is_ok() is true
   - Expected: rv32_module.shape_diagnostic() equals ``
   - Expected: rv64_module.shape_diagnostic() equals ``
   - Expected: strict_has_signal(rv32_module, "global_no_overlap") is true
   - Expected: strict_has_signal(rv64_module, "global_no_overlap") is true
   - Expected: rv64_overlap_origin_count equals `1`
   - Expected: strict_output_driver_count(rv32_module, "legal") equals `1`
   - Expected: strict_output_driver_count(rv64_module, "legal") equals `1`
   - Expected: strict_output_driver_count(rv32_module, "trap_valid") equals `1`
   - Expected: strict_output_driver_count(rv64_module, "trap_valid") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should bind each specialized trap frontend and decoder to one closed no-overlap graph")
step("Lower concrete RV32 C.JAL and RV64 C.ADDIW trap products with their selected decoder identities")
val rv32_config = CoreConfig.rv32_zca_cjal_mission_critical()
val rv64_config = CoreConfig.rv64_zca_addiw_mission_critical()
val rv32_decoder = strict_zca_target_trap_migrating_predecode_hwir(
    "riscv_gen2_zca_rv32_cjal_trap_migrating_predecode", rv32_config)
val rv64_decoder = strict_zca_target_trap_migrating_predecode_hwir(
    "riscv_gen2_zca_rv64_addiw_trap_migrating_predecode", rv64_config)
val rv32_frontend = strict_zca_trap_single_outstanding_frontend_hwir(
    "riscv_gen2_zca_rv32_cjal_trap_single_outstanding_frontend", rv32_config)
val rv64_frontend = strict_zca_trap_single_outstanding_frontend_hwir(
    "riscv_gen2_zca_rv64_addiw_trap_single_outstanding_frontend", rv64_config)
expect(rv32_decoder.is_ok()).to_equal(true)
expect(rv64_decoder.is_ok()).to_equal(true)
expect(rv32_frontend.is_ok()).to_equal(true)
expect(rv64_frontend.is_ok()).to_equal(true)
val rv32_module = rv32_decoder.ok().unwrap()
val rv64_module = rv64_decoder.ok().unwrap()
expect(rv32_module.shape_diagnostic()).to_equal("")
expect(rv64_module.shape_diagnostic()).to_equal("")
expect(strict_has_signal(rv32_module, "global_no_overlap")).to_equal(true)
expect(strict_has_signal(rv64_module, "global_no_overlap")).to_equal(true)
var rv64_overlap_origin_count = 0
for origin in rv64_module.origins:
    if origin.source_name.ends_with(".overlap_guard"):
        rv64_overlap_origin_count = rv64_overlap_origin_count + 1
expect(rv64_overlap_origin_count).to_equal(1)
expect(strict_output_driver_count(rv32_module, "legal")).to_equal(1)
expect(strict_output_driver_count(rv64_module, "legal")).to_equal(1)
expect(strict_output_driver_count(rv32_module, "trap_valid")).to_equal(1)
expect(strict_output_driver_count(rv64_module, "trap_valid")).to_equal(1)
expect(rv32_frontend.ok().unwrap().decoder_entity).to_equal(
    "riscv_gen2_zca_rv32_cjal_trap_migrating_predecode")
expect(rv64_frontend.ok().unwrap().decoder_entity).to_equal(
    "riscv_gen2_zca_rv64_addiw_trap_migrating_predecode")
```

</details>

#### REQ-G2-010 rejects a stateful frontend whose decoder is not the concrete typed child

- REQ-G2-010 rejects a stateful frontend whose decoder is not the concrete typed child
- Verify: REQ-G2-010 rejects a stateful frontend whose decoder is not the concrete typed child
   - Expected: product.shape_diagnostic() equals `HWIR-E-TRAP-PARCEL-FRONTEND-DECODER: trap frontend decoder identity must matc... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-010 rejects a stateful frontend whose decoder is not the concrete typed child")
step("Verify: REQ-G2-010 rejects a stateful frontend whose decoder is not the concrete typed child")
val config = CoreConfig.rv32_zca_mission_critical()
val frontend = strict_zca_trap_single_outstanding_frontend_hwir("trap_decoder_identity", config)
if val product = frontend.ok():
    product.decoder_entity = "unbound_decoder"
    expect(product.shape_diagnostic()).to_equal("HWIR-E-TRAP-PARCEL-FRONTEND-DECODER: trap frontend decoder identity must match the concrete critical product")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-010 rejects malformed sequential bindings and commits decoder identity into the graph hash

- REQ-G2-010 rejects malformed sequential bindings and commits decoder identity into the graph hash
- Verify: REQ-G2-010 rejects malformed sequential bindings and commits decoder identity into the graph hash
   - Expected: duplicate_pin_plan.diagnostic_for_ports(product.frontend_contract.ports()) equals `HWIR-E-SEQUENTIAL-INSTANCE: decoder pins must be typed inputs or outputs`
   - Expected: invalid_output_plan.diagnostic_for_ports(product.frontend_contract.ports()) equals `HWIR-E-SEQUENTIAL-OUTPUT: sequential bindings must drive matching public outputs`
   - Expected: graph.len() equals `64`
   - Expected: graph == changed_decoder_graph is false
   - Expected: changed_guard_plan.diagnostic_for_ports(product.frontend_contract.ports()) equals ``
   - Expected: product.sequential.canonical_text() == changed_guard_plan.canonical_text() is false
   - Expected: graph == changed_guard_graph is false
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-010 rejects malformed sequential bindings and commits decoder identity into the graph hash")
step("Verify: REQ-G2-010 rejects malformed sequential bindings and commits decoder identity into the graph hash")
val config = CoreConfig.rv32_zca_mission_critical()
val frontend = strict_zca_trap_single_outstanding_frontend_hwir("trap_sequential_contract", config)
if val product = frontend.ok():
    var duplicate_pins = product.sequential.decoder_pins
    duplicate_pins.push(HwSeqInstancePin(port_name: "original_parcel", signal_name: "parcel_duplicate", direction: "in", bit_width: 16))
    val duplicate_pin_plan = HwSequentialPlan(owner_id: product.sequential.owner_id,
        registers: product.sequential.registers, rules: product.sequential.rules,
        outputs: product.sequential.outputs, decoder_pins: duplicate_pins)
    expect(duplicate_pin_plan.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("HWIR-E-SEQUENTIAL-INSTANCE: decoder pins must be typed inputs or outputs")

    val invalid_output_plan = HwSequentialPlan(owner_id: product.sequential.owner_id,
        registers: product.sequential.registers, rules: product.sequential.rules,
        outputs: [HwSeqOutputBinding.direct("fetch_ready", "valid_reg", 2)],
        decoder_pins: product.sequential.decoder_pins)
    expect(invalid_output_plan.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("HWIR-E-SEQUENTIAL-OUTPUT: sequential bindings must drive matching public outputs")

    val graph = strict_stateful_graph_sha(product.node_id.value, product.config,
        product.origins, product.frontend_contract.ports(), product.decoder_entity,
        product.sequential, "decoder-graph-a")
    val changed_decoder_graph = strict_stateful_graph_sha(product.node_id.value,
        product.config, product.origins, product.frontend_contract.ports(),
        "riscv_gen2_zca_trap_migrating_predecode_rv64", product.sequential,
        "decoder-graph-a")
    expect(graph.len()).to_equal(64)
    expect(graph == changed_decoder_graph).to_equal(false)

    var changed_outputs = product.sequential.outputs
    var changed_ready = changed_outputs[0]
    changed_ready.guards = [HwSeqGuard.high("valid_reg"), HwSeqGuard.low("fault_reg")]
    changed_outputs[0] = changed_ready
    val changed_guard_plan = HwSequentialPlan(owner_id: product.sequential.owner_id,
        registers: product.sequential.registers, rules: product.sequential.rules,
        outputs: changed_outputs, decoder_pins: product.sequential.decoder_pins)
    expect(changed_guard_plan.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("")
    val changed_guard_graph = strict_stateful_graph_sha(product.node_id.value,
        product.config, product.origins, product.frontend_contract.ports(),
        product.decoder_entity, changed_guard_plan, "decoder-graph-a")
    expect(product.sequential.canonical_text() == changed_guard_plan.canonical_text()).to_equal(false)
    expect(graph == changed_guard_graph).to_equal(false)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects case-only sequential names before VHDL serialization

- rejects case-only sequential names before VHDL serialization
- Verify: rejects case-only sequential names before VHDL serialization
   - Expected: product.sequential.diagnostic() equals `HWIR-E-SEQUENTIAL-REGISTER: sequential registers must be unique and valid`
   - Expected: false is true
   - Expected: product.sequential.diagnostic() equals `HWIR-E-SEQUENTIAL-RULE: sequential rules require unique names, guards, and as... (full value in folded executable source)`
   - Expected: false is true
   - Expected: product.sequential.diagnostic_for_ports(product.frontend_contract.ports()) equals `HWIR-E-SEQUENTIAL-INSTANCE: decoder pins must be typed inputs or outputs`
   - Expected: false is true
   - Expected: product.sequential.diagnostic_for_ports(product.frontend_contract.ports()) equals `HWIR-E-SEQUENTIAL-OUTPUT: sequential bindings must drive matching public outputs`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects case-only sequential names before VHDL serialization")
step("Verify: rejects case-only sequential names before VHDL serialization")
val config = CoreConfig.rv32_zca_mission_critical()
val register_product = strict_zca_trap_single_outstanding_frontend_hwir("casefold_register", config)
if val product = register_product.ok():
    product.sequential.registers[1].name = "VALID_REG"
    expect(product.sequential.diagnostic()).to_equal("HWIR-E-SEQUENTIAL-REGISTER: sequential registers must be unique and valid")
else:
    expect(false).to_equal(true)

val rule_product = strict_zca_trap_single_outstanding_frontend_hwir("casefold_rule", config)
if val product = rule_product.ok():
    product.sequential.rules[1].name = "RETIRE_MATCH"
    expect(product.sequential.diagnostic()).to_equal("HWIR-E-SEQUENTIAL-RULE: sequential rules require unique names, guards, and assignments")
else:
    expect(false).to_equal(true)

val pin_product = strict_zca_trap_single_outstanding_frontend_hwir("casefold_pin", config)
if val product = pin_product.ok():
    product.sequential.decoder_pins[1].port_name = "ORIGINAL_PARCEL"
    expect(product.sequential.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("HWIR-E-SEQUENTIAL-INSTANCE: decoder pins must be typed inputs or outputs")
else:
    expect(false).to_equal(true)

val output_product = strict_zca_trap_single_outstanding_frontend_hwir("casefold_output", config)
if val product = output_product.ok():
    product.sequential.outputs[1].result = "FETCH_READY"
    expect(product.sequential.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("HWIR-E-SEQUENTIAL-OUTPUT: sequential bindings must drive matching public outputs")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-002 rejects every concrete configuration boundary before strict predecode construction

- REQ-G2-002 rejects every concrete configuration boundary before strict predecode construction
- Verify: REQ-G2-002 rejects every concrete configuration boundary before strict predecode construction
   - Expected: strict_riscv_predecode_interface(invalid_pa).is_err() is true
   - Expected: strict_riscv_predecode_interface(invalid_register_count).is_err() is true
   - Expected: strict_riscv_predecode_interface(unsafe_profile).is_err() is true
   - Expected: strict_riscv_predecode_interface(unknown_compressed).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-002 rejects every concrete configuration boundary before strict predecode construction")
step("Verify: REQ-G2-002 rejects every concrete configuration boundary before strict predecode construction")
val invalid_pa = CoreConfig(xlen: 32, physical_address_bits: 15,
    register_count: 32, profile: "rv32-critical", isa_profile: "rv32i",
    compressed_decode_profile: "none")
expect(invalid_pa.diagnostic()).to_equal(
    "HWIR-E-CONFIG-PA: physical address width must be in 16..64")

val invalid_register_count = CoreConfig(xlen: 32, physical_address_bits: 32,
    register_count: 16, profile: "rv32-critical", isa_profile: "rv32i",
    compressed_decode_profile: "none")
expect(invalid_register_count.diagnostic()).to_equal(
    "HWIR-E-CONFIG-REGISTERS: strict RISC-V HWIR requires 32 architectural registers")

val unsafe_profile = CoreConfig(xlen: 32, physical_address_bits: 32,
    register_count: 32, profile: "rv32 critical", isa_profile: "rv32i",
    compressed_decode_profile: "none")
expect(unsafe_profile.diagnostic()).to_equal(
    "HWIR-E-CONFIG-PROFILE: strict RISC-V HWIR requires safe concrete profile names")

val unknown_compressed = CoreConfig(xlen: 32, physical_address_bits: 32,
    register_count: 32, profile: "rv32-critical", isa_profile: "rv32i",
    compressed_decode_profile: "zcb-unadmitted")
expect(unknown_compressed.diagnostic()).to_equal(
    "HWIR-E-CONFIG-COMPRESSED: unsupported strict compressed profile")

expect(strict_riscv_predecode_interface(invalid_pa).is_err()).to_equal(true)
expect(strict_riscv_predecode_interface(invalid_register_count).is_err()).to_equal(true)
expect(strict_riscv_predecode_interface(unsafe_profile).is_err()).to_equal(true)
expect(strict_riscv_predecode_interface(unknown_compressed).is_err()).to_equal(true)
```

</details>

#### REQ-G2-010 commits config, lineage, public ports, decoder identity, and decoder digest into the stateful graph hash

- REQ-G2-010 commits config, lineage, public ports, decoder identity, and decoder digest into the stateful graph hash
- Verify: REQ-G2-010 commits config, lineage, public ports, decoder identity, and decoder digest into the stateful graph hash
   - Expected: baseline.len() equals `64`
   - Expected: baseline == config_mutation is false
   - Expected: baseline == origin_mutation is false
   - Expected: baseline == port_mutation is false
   - Expected: baseline == decoder_digest_mutation is false
   - Expected: baseline == decoder_entity_mutation is false
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-010 commits config, lineage, public ports, decoder identity, and decoder digest into the stateful graph hash")
step("Verify: REQ-G2-010 commits config, lineage, public ports, decoder identity, and decoder digest into the stateful graph hash")
val frontend = strict_zca_trap_single_outstanding_frontend_hwir(
    "trap_graph_closure", CoreConfig.rv32_zca_mission_critical())
if val product = frontend.ok():
    val baseline = strict_stateful_graph_sha(product.node_id.value, product.config,
        product.origins, product.frontend_contract.ports(), product.decoder_entity,
        product.sequential, "decoder-graph-a")

    var changed_config = product.config
    changed_config.physical_address_bits = 33
    val config_mutation = strict_stateful_graph_sha(product.node_id.value,
        changed_config, product.origins, product.frontend_contract.ports(),
        product.decoder_entity, product.sequential, "decoder-graph-a")

    var changed_origins = product.origins
    changed_origins[0].source_name = changed_origins[0].source_name + ".mutated"
    val origin_mutation = strict_stateful_graph_sha(product.node_id.value,
        product.config, changed_origins, product.frontend_contract.ports(),
        product.decoder_entity, product.sequential, "decoder-graph-a")

    var changed_ports = product.frontend_contract.ports()
    changed_ports[0].clock_domain = "derived"
    val port_mutation = strict_stateful_graph_sha(product.node_id.value,
        product.config, product.origins, changed_ports, product.decoder_entity,
        product.sequential, "decoder-graph-a")

    val decoder_digest_mutation = strict_stateful_graph_sha(product.node_id.value,
        product.config, product.origins, product.frontend_contract.ports(),
        product.decoder_entity, product.sequential, "decoder-graph-b")
    val decoder_entity_mutation = strict_stateful_graph_sha(product.node_id.value,
        product.config, product.origins, product.frontend_contract.ports(),
        "riscv_gen2_zca_trap_migrating_predecode_rv64", product.sequential,
        "decoder-graph-a")

    expect(baseline.len()).to_equal(64)
    expect(baseline == config_mutation).to_equal(false)
    expect(baseline == origin_mutation).to_equal(false)
    expect(baseline == port_mutation).to_equal(false)
    expect(baseline == decoder_digest_mutation).to_equal(false)
    expect(baseline == decoder_entity_mutation).to_equal(false)
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-010 rejects case-only public port collisions before VHDL emission

- REQ-G2-010 rejects case-only public port collisions before VHDL emission
- Verify: REQ-G2-010 rejects case-only public port collisions before VHDL emission
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-010 rejects case-only public port collisions before VHDL emission")
step("Verify: REQ-G2-010 rejects case-only public port collisions before VHDL emission")
val plain = strict_riscv_parcel_frontend_interface(CoreConfig.rv32_zca_mission_critical())
if val contract = plain.ok():
    contract.rst.name = "CLK"
    expect(contract.shape_diagnostic()).to_equal(
        "HWIR-E-PARCEL-FRONTEND-DUPLICATE-PORT: stateful frontend port names must be unique")
else:
    expect(false).to_equal(true)

val trap = strict_riscv_trap_parcel_frontend_interface(CoreConfig.rv32_zca_mission_critical())
if val contract = trap.ok():
    contract.rst.name = "CLK"
    expect(contract.shape_diagnostic()).to_equal(
        "HWIR-E-TRAP-PARCEL-FRONTEND-DUPLICATE-PORT: trap frontend port names must be unique")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-010 rejects type-correct sequential rule ordering and reset drift from the fixed trap product

- REQ-G2-010 rejects type-correct sequential rule ordering and reset drift from the fixed trap product
- Verify: REQ-G2-010 rejects type-correct sequential rule ordering and reset drift from the fixed trap product
   - Expected: reordered_plan.diagnostic_for_ports(product.frontend_contract.ports()) equals ``
   - Expected: product.shape_diagnostic() equals `HWIR-E-TRAP-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE: trap frontend sequential pla... (full value in folded executable source)`
   - Expected: changed_reset_plan.diagnostic_for_ports(product.frontend_contract.ports()) equals ``
   - Expected: product.shape_diagnostic() equals `HWIR-E-TRAP-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE: trap frontend sequential pla... (full value in folded executable source)`
   - Expected: weakened_guard_plan.diagnostic_for_ports(product.frontend_contract.ports()) equals ``
   - Expected: product.shape_diagnostic() equals `HWIR-E-TRAP-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE: trap frontend sequential pla... (full value in folded executable source)`
   - Expected: malformed_exhaustion_plan.diagnostic_for_ports(product.frontend_contract.ports()) equals `HWIR-E-SEQUENTIAL-GUARD: all-ones guards require multi-bit typed values`
   - Expected: bypass_exhaustion_plan.diagnostic_for_ports(product.frontend_contract.ports()) equals ``
   - Expected: product.shape_diagnostic() equals `HWIR-E-TRAP-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE: trap frontend sequential pla... (full value in folded executable source)`
   - Expected: duplicate_output_plan.diagnostic_for_ports(product.frontend_contract.ports()) equals `HWIR-E-SEQUENTIAL-OUTPUT: sequential bindings must drive matching public outputs`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-010 rejects type-correct sequential rule ordering and reset drift from the fixed trap product")
step("Verify: REQ-G2-010 rejects type-correct sequential rule ordering and reset drift from the fixed trap product")
val config = CoreConfig.rv32_zca_mission_critical()
val frontend = strict_zca_trap_single_outstanding_frontend_hwir("trap_sequential_template", config)
if val product = frontend.ok():
    val canonical_plan = product.sequential
    var reordered_rules = canonical_plan.rules
    val first_rule = reordered_rules[0]
    reordered_rules[0] = reordered_rules[1]
    reordered_rules[1] = first_rule
    val reordered_plan = HwSequentialPlan(owner_id: canonical_plan.owner_id,
        registers: canonical_plan.registers, rules: reordered_rules,
        outputs: canonical_plan.outputs, decoder_pins: canonical_plan.decoder_pins)
    expect(reordered_plan.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("")
    product.sequential = reordered_plan
    expect(product.shape_diagnostic()).to_equal("HWIR-E-TRAP-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE: trap frontend sequential plan must exactly match the selected fixed critical product")

    var changed_registers = canonical_plan.registers
    var changed_valid = changed_registers[0]
    changed_valid.reset_value = 1
    changed_registers[0] = changed_valid
    val changed_reset_plan = HwSequentialPlan(owner_id: canonical_plan.owner_id,
        registers: changed_registers, rules: canonical_plan.rules,
        outputs: canonical_plan.outputs, decoder_pins: canonical_plan.decoder_pins)
    expect(changed_reset_plan.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("")
    product.sequential = changed_reset_plan
    expect(product.shape_diagnostic()).to_equal("HWIR-E-TRAP-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE: trap frontend sequential plan must exactly match the selected fixed critical product")

    var weakened_rules = canonical_plan.rules
    var weakened_retire_match = weakened_rules[1]
    weakened_retire_match.guards = [HwSeqGuard.high("retire_valid"),
        HwSeqGuard.high("valid_reg"), HwSeqGuard.high("issued_reg"),
        HwSeqGuard.equal("lineage_reg", "lineage_reg")]
    weakened_rules[1] = weakened_retire_match
    val weakened_guard_plan = HwSequentialPlan(owner_id: canonical_plan.owner_id,
        registers: canonical_plan.registers, rules: weakened_rules,
        outputs: canonical_plan.outputs, decoder_pins: canonical_plan.decoder_pins)
    expect(weakened_guard_plan.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("")
    product.sequential = weakened_guard_plan
    expect(product.shape_diagnostic()).to_equal("HWIR-E-TRAP-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE: trap frontend sequential plan must exactly match the selected fixed critical product")

    var malformed_exhaustion_rules = canonical_plan.rules
    var malformed_exhaustion = malformed_exhaustion_rules[0]
    malformed_exhaustion.guards[7] = HwSeqGuard.all_ones("valid_reg")
    malformed_exhaustion_rules[0] = malformed_exhaustion
    val malformed_exhaustion_plan = HwSequentialPlan(owner_id: canonical_plan.owner_id,
        registers: canonical_plan.registers, rules: malformed_exhaustion_rules,
        outputs: canonical_plan.outputs, decoder_pins: canonical_plan.decoder_pins)
    expect(malformed_exhaustion_plan.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("HWIR-E-SEQUENTIAL-GUARD: all-ones guards require multi-bit typed values")

    var bypass_exhaustion_rules = canonical_plan.rules
    var bypass_exhaustion = bypass_exhaustion_rules[0]
    bypass_exhaustion.guards[7] = HwSeqGuard.equal("lineage_reg", "lineage_reg")
    bypass_exhaustion_rules[0] = bypass_exhaustion
    val bypass_exhaustion_plan = HwSequentialPlan(owner_id: canonical_plan.owner_id,
        registers: canonical_plan.registers, rules: bypass_exhaustion_rules,
        outputs: canonical_plan.outputs, decoder_pins: canonical_plan.decoder_pins)
    expect(bypass_exhaustion_plan.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("")
    product.sequential = bypass_exhaustion_plan
    expect(product.shape_diagnostic()).to_equal("HWIR-E-TRAP-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE: trap frontend sequential plan must exactly match the selected fixed critical product")

    var duplicate_outputs = canonical_plan.outputs
    duplicate_outputs.push(HwSeqOutputBinding.direct("protocol_fault", "fault_reg", 1))
    val duplicate_output_plan = HwSequentialPlan(owner_id: canonical_plan.owner_id,
        registers: canonical_plan.registers, rules: canonical_plan.rules,
        outputs: duplicate_outputs, decoder_pins: canonical_plan.decoder_pins)
    expect(duplicate_output_plan.diagnostic_for_ports(product.frontend_contract.ports())).to_equal("HWIR-E-SEQUENTIAL-OUTPUT: sequential bindings must drive matching public outputs")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-011 keeps C.EBREAK as a legal breakpoint effect in the versioned trap contract

- REQ-G2-011 keeps C.EBREAK as a legal breakpoint effect in the versioned trap contract
- Verify: REQ-G2-011 keeps C.EBREAK as a legal breakpoint effect in the versioned trap contract
   - Expected: interface32.shape_diagnostic() equals ``
   - Expected: interface32.ports().len() equals `13`
   - Expected: interface32.trap_valid.bit_width equals `1`
   - Expected: interface32.trap_cause.bit_width equals `32`
   - Expected: interface32.trap_tval.bit_width equals `32`
   - Expected: false is true
   - Expected: interface64.trap_cause.bit_width equals `64`
   - Expected: interface64.trap_tval.bit_width equals `64`
   - Expected: false is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: strict_origin_source_count(module, "zca.c.ebreak.trap") equals `1`
   - Expected: strict_output_driver_count(module, "legal") equals `1`
   - Expected: strict_output_driver_count(module, "trap_valid") equals `1`
   - Expected: strict_output_driver_count(module, "trap_cause") equals `1`
   - Expected: strict_output_driver_count(module, "trap_tval") equals `1`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-011 keeps C.EBREAK as a legal breakpoint effect in the versioned trap contract")
step("Verify: REQ-G2-011 keeps C.EBREAK as a legal breakpoint effect in the versioned trap contract")
val rv32 = strict_riscv_trap_predecode_interface(CoreConfig.rv32_zca_mission_critical())
val rv64 = strict_riscv_trap_predecode_interface(CoreConfig.rv64_zca_mission_critical())
if val interface32 = rv32.ok():
    expect(interface32.shape_diagnostic()).to_equal("")
    expect(interface32.ports().len()).to_equal(13)
    expect(interface32.trap_valid.bit_width).to_equal(1)
    expect(interface32.trap_cause.bit_width).to_equal(32)
    expect(interface32.trap_tval.bit_width).to_equal(32)
else:
    expect(false).to_equal(true)
if val interface64 = rv64.ok():
    expect(interface64.trap_cause.bit_width).to_equal(64)
    expect(interface64.trap_tval.bit_width).to_equal(64)
else:
    expect(false).to_equal(true)
val row = strict_zca_cebreak_trap_predecode_hwir("strict_cebreak_trap", CoreConfig.rv32_zca_mission_critical())
if val module = row.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(strict_origin_source_count(module, "zca.c.ebreak.trap")).to_equal(1)
    expect(strict_output_driver_count(module, "legal")).to_equal(1)
    expect(strict_output_driver_count(module, "trap_valid")).to_equal(1)
    expect(strict_output_driver_count(module, "trap_cause")).to_equal(1)
    expect(strict_output_driver_count(module, "trap_tval")).to_equal(1)
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_be(true)
    expect(emitted.vhdl.contains("breakpoint_cause")).to_be(true)
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-003 rejects malformed C.EBREAK trap-effect ports before emission

- REQ-G2-003 rejects malformed C.EBREAK trap-effect ports before emission
- Verify: REQ-G2-003 rejects malformed C.EBREAK trap-effect ports before emission
   - Expected: malformed.shape_diagnostic() equals `HWIR-E-TRAP-PREDECODE-CAUSE: trap predecode requires an XLEN-wide Bits trap_c... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-003 rejects malformed C.EBREAK trap-effect ports before emission")
step("Verify: REQ-G2-003 rejects malformed C.EBREAK trap-effect ports before emission")
val config = CoreConfig.rv32_zca_mission_critical()
val branch = strict_riscv_branch_predecode_interface(config)
if val branch_contract = branch.ok():
    val malformed = HwTrapPredecodeInterface(
        node_id: HwNodeId.module_root("riscv_trap_predecode"), config: config,
        branch_predecode: branch_contract,
        trap_valid: HwPort.output("trap_valid", "Bits", 1),
        trap_cause: HwPort.output("trap_cause", "Bits", 31),
        trap_tval: HwPort.output("trap_tval", "Bits", 32)
    )
    expect(malformed.shape_diagnostic()).to_equal("HWIR-E-TRAP-PREDECODE-CAUSE: trap predecode requires an XLEN-wide Bits trap_cause output")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-011 composes admitted outcome rows with the branch-control slice through one legal-priority chain

- REQ-G2-011 composes admitted outcome rows with the branch-control slice through one legal-priority chain
- Verify: REQ-G2-011 composes admitted outcome rows with the branch-control slice through one legal-priority chain
   - Expected: module32.shape_diagnostic() equals ``
   - Expected: module64.shape_diagnostic() equals ``
   - Expected: module32.port_width("rs1_value") equals `32`
   - Expected: module64.port_width("rs1_value") equals `64`
   - Expected: strict_origin_source_count(module32, "riscv.gen2.migrating_predecode") equals `1`
   - Expected: strict_output_driver_count(module32, "canonical_instruction") equals `1`
   - Expected: strict_output_driver_count(module32, "legal") equals `1`
   - Expected: strict_output_driver_count(module32, "next_pc") equals `1`
   - Expected: strict_output_driver_count(module32, "redirect_valid") equals `1`
   - Expected: strict_output_driver_count(module32, "redirect_target") equals `1`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-011 composes admitted outcome rows with the branch-control slice through one legal-priority chain")
step("Verify: REQ-G2-011 composes admitted outcome rows with the branch-control slice through one legal-priority chain")
val rv32 = strict_zca_migrating_predecode_hwir("migrating_predecode_rv32", CoreConfig.rv32_zca_mission_critical())
val rv64 = strict_zca_migrating_predecode_hwir("migrating_predecode_rv64", CoreConfig.rv64_zca_mission_critical())
if rv32.is_ok() and rv64.is_ok():
    val module32 = rv32.ok().unwrap()
    val module64 = rv64.ok().unwrap()
    expect(module32.shape_diagnostic()).to_equal("")
    expect(module64.shape_diagnostic()).to_equal("")
    expect(module32.port_width("rs1_value")).to_equal(32)
    expect(module64.port_width("rs1_value")).to_equal(64)
    expect(strict_origin_source_count(module32, "riscv.gen2.migrating_predecode")).to_equal(1)
    expect(strict_origin_source_count(module32, "zca.c.lw.outcome")).to_be_greater_than(0)
    expect(strict_origin_source_count(module32, "zca.c.addi16sp.outcome")).to_be_greater_than(0)
    expect(strict_origin_source_count(module32, "zca.c.jr.predecode")).to_be_greater_than(0)
    expect(strict_origin_source_count(module32, "zca.c.jalr.predecode")).to_be_greater_than(0)
    expect(strict_origin_source_count(module32, "zca.c.lwsp.outcome")).to_be_greater_than(0)
    expect(strict_output_driver_count(module32, "canonical_instruction")).to_equal(1)
    expect(strict_output_driver_count(module32, "legal")).to_equal(1)
    expect(strict_output_driver_count(module32, "next_pc")).to_equal(1)
    expect(strict_output_driver_count(module32, "redirect_valid")).to_equal(1)
    expect(strict_output_driver_count(module32, "redirect_target")).to_equal(1)
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-011 admits only classifier-complete normal rows through the explicit outcome adapter

- REQ-G2-011 admits only classifier-complete normal rows through the explicit outcome adapter
- Verify: REQ-G2-011 admits only classifier-complete normal rows through the explicit outcome adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-011 admits only classifier-complete normal rows through the explicit outcome adapter")
step("Verify: REQ-G2-011 admits only classifier-complete normal rows through the explicit outcome adapter")
val config = CoreConfig.rv32_zca_mission_critical()
expect(strict_zca_addi4spn_outcome_hwir("outcome_addi4spn", config).is_ok()).to_be(true)
expect(strict_zca_lw_outcome_hwir("outcome_lw", config).is_ok()).to_be(true)
expect(strict_zca_sw_outcome_hwir("outcome_sw", config).is_ok()).to_be(true)
expect(strict_zca_lwsp_outcome_hwir("outcome_lwsp", config).is_ok()).to_be(true)
expect(strict_zca_swsp_outcome_hwir("outcome_swsp", config).is_ok()).to_be(true)
expect(strict_zca_cli_outcome_hwir("outcome_cli", config).is_ok()).to_be(true)
expect(strict_zca_caddi_outcome_hwir("outcome_caddi", config).is_ok()).to_be(true)
expect(strict_zca_caddi16sp_outcome_hwir("outcome_caddi16sp", config).is_ok()).to_be(true)
expect(strict_zca_clui_outcome_hwir("outcome_clui", config).is_ok()).to_be(true)
expect(strict_zca_slli_low_outcome_hwir("outcome_slli", config).is_ok()).to_be(true)
expect(strict_zca_srli_low_outcome_hwir("outcome_srli", config).is_ok()).to_be(true)
expect(strict_zca_srai_low_outcome_hwir("outcome_srai", config).is_ok()).to_be(true)
expect(strict_zca_candi_outcome_hwir("outcome_candi", config).is_ok()).to_be(true)
expect(strict_zca_csub_outcome_hwir("outcome_csub", config).is_ok()).to_be(true)
expect(strict_zca_cxor_outcome_hwir("outcome_cxor", config).is_ok()).to_be(true)
expect(strict_zca_cor_outcome_hwir("outcome_cor", config).is_ok()).to_be(true)
expect(strict_zca_cand_outcome_hwir("outcome_cand", config).is_ok()).to_be(true)
expect(strict_zca_cmv_outcome_hwir("outcome_cmv", config).is_ok()).to_be(true)
expect(strict_zca_cadd_outcome_hwir("outcome_cadd", config).is_ok()).to_be(true)
expect(strict_zca_lw_outcome_hwir("outcome_base", CoreConfig.rv32()).is_err()).to_be(true)
```

</details>

#### REQ-G2-011 gives every normal outcome an explicit legality, fallthrough, and effect contract

- REQ-G2-011 gives every normal outcome an explicit legality, fallthrough, and effect contract
- Verify: REQ-G2-011 gives every normal outcome an explicit legality, fallthrough, and effect contract
   - Expected: strict_comb_source(lw, "effect_memory_read") equals `match_legal`
   - Expected: strict_comb_source(sw, "effect_memory_write") equals `match_legal`
   - Expected: strict_comb_source(addi, "effect_register_write") equals `match_legal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-011 gives every normal outcome an explicit legality, fallthrough, and effect contract")
step("Verify: REQ-G2-011 gives every normal outcome an explicit legality, fallthrough, and effect contract")
val config = CoreConfig.rv32_zca_mission_critical()
val outcomes = [
    strict_zca_addi4spn_outcome_hwir("contract_addi4spn", config).ok().unwrap(),
    strict_zca_lw_outcome_hwir("contract_lw", config).ok().unwrap(),
    strict_zca_sw_outcome_hwir("contract_sw", config).ok().unwrap(),
    strict_zca_lwsp_outcome_hwir("contract_lwsp", config).ok().unwrap(),
    strict_zca_swsp_outcome_hwir("contract_swsp", config).ok().unwrap(),
    strict_zca_cli_outcome_hwir("contract_cli", config).ok().unwrap(),
    strict_zca_caddi_outcome_hwir("contract_addi", config).ok().unwrap(),
    strict_zca_caddi16sp_outcome_hwir("contract_addi16sp", config).ok().unwrap(),
    strict_zca_clui_outcome_hwir("contract_lui", config).ok().unwrap(),
    strict_zca_slli_low_outcome_hwir("contract_slli", config).ok().unwrap(),
    strict_zca_srli_low_outcome_hwir("contract_srli", config).ok().unwrap(),
    strict_zca_srai_low_outcome_hwir("contract_srai", config).ok().unwrap(),
    strict_zca_candi_outcome_hwir("contract_andi", config).ok().unwrap(),
    strict_zca_csub_outcome_hwir("contract_sub", config).ok().unwrap(),
    strict_zca_cxor_outcome_hwir("contract_xor", config).ok().unwrap(),
    strict_zca_cor_outcome_hwir("contract_or", config).ok().unwrap(),
    strict_zca_cand_outcome_hwir("contract_and", config).ok().unwrap(),
    strict_zca_cmv_outcome_hwir("contract_mv", config).ok().unwrap(),
    strict_zca_cadd_outcome_hwir("contract_add", config).ok().unwrap()
]
for outcome in outcomes:
    expect_normal_outcome_contract(outcome)
val lw = outcomes[1]
val sw = outcomes[2]
val addi = outcomes[6]
expect(strict_comb_source(lw, "effect_memory_read")).to_equal("match_legal")
expect(strict_comb_source(sw, "effect_memory_write")).to_equal("match_legal")
expect(strict_comb_source(addi, "effect_register_write")).to_equal("match_legal")
```

</details>

#### REQ-G2-011 keeps C.MV and C.ADD disjoint from JR JALR and EBREAK boundaries

- REQ-G2-011 keeps C.MV and C.ADD disjoint from JR JALR and EBREAK boundaries
- Verify: REQ-G2-011 keeps C.MV and C.ADD disjoint from JR JALR and EBREAK boundaries
   - Expected: 32898 & 61443 equals `32770`
   - Expected: 36994 & 61443 equals `36866`
   - Expected: 36866 & 61443 equals `36866`
   - Expected: strict_select_condition(cmv, "cmv_legal_after_reserved_0") equals `cmv_rs2_is_zero`
   - Expected: strict_select_condition(cmv, "match_legal") equals `cmv_is_c_mv`
   - Expected: strict_select_condition(cadd, "cadd_legal_after_reserved_0") equals `cadd_rs2_is_zero`
   - Expected: strict_select_condition(cadd, "match_legal") equals `cadd_is_c_add`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-011 keeps C.MV and C.ADD disjoint from JR JALR and EBREAK boundaries")
step("Verify: REQ-G2-011 keeps C.MV and C.ADD disjoint from JR JALR and EBREAK boundaries")
val config = CoreConfig.rv32_zca_mission_critical()
# 0x8082 (JR x1), 0x9082 (JALR x1), and 0x9002 (EBREAK) share
# the coarse normal-row tags. Their rs2 field is zero, so the explicit
# reserved gate below, rather than a canonical-word sentinel, excludes them.
expect(32898 & 61443).to_equal(32770)
expect(36994 & 61443).to_equal(36866)
expect(36866 & 61443).to_equal(36866)
val cmv = strict_zca_cmv_outcome_hwir("boundary_cmv", config).ok().unwrap()
val cadd = strict_zca_cadd_outcome_hwir("boundary_cadd", config).ok().unwrap()
expect(strict_select_condition(cmv, "cmv_legal_after_reserved_0")).to_equal("cmv_rs2_is_zero")
expect(strict_select_condition(cmv, "match_legal")).to_equal("cmv_is_c_mv")
expect(strict_select_condition(cadd, "cadd_legal_after_reserved_0")).to_equal("cadd_rs2_is_zero")
expect(strict_select_condition(cadd, "match_legal")).to_equal("cadd_is_c_add")
val cmv_vhdl = render_strict_hwir_vhdl(cmv)
val cadd_vhdl = render_strict_hwir_vhdl(cadd)
expect(cmv_vhdl.is_success()).to_be(true)
expect(cadd_vhdl.is_success()).to_be(true)
expect(cmv_vhdl.vhdl).to_contain("cmv_legal_after_reserved_0 <= zero_flag when cmv_rs2_is_zero = '1'")
expect(cadd_vhdl.vhdl).to_contain("cadd_legal_after_reserved_0 <= zero_flag when cadd_rs2_is_zero = '1'")
```

</details>

#### REQ-G2-003 concretely specializes address widths without runtime XLEN selection

- REQ-G2-003 concretely specializes address widths without runtime XLEN selection
- Verify: REQ-G2-003 concretely specializes address widths without runtime XLEN selection
   - Expected: interface32.shape_diagnostic() equals ``
   - Expected: interface32.original_parcel.bit_width equals `16`
   - Expected: interface32.fetch_pc.bit_width equals `32`
   - Expected: interface32.canonical_instruction.bit_width equals `32`
   - Expected: interface32.original_length_bytes.bit_width equals `2`
   - Expected: interface32.next_pc.bit_width equals `32`
   - Expected: interface32.redirect_target.bit_width equals `32`
   - Expected: false is true
   - Expected: interface64.fetch_pc.bit_width equals `56`
   - Expected: interface64.next_pc.bit_width equals `56`
   - Expected: interface64.redirect_target.bit_width equals `56`
   - Expected: interface64.config.xlen equals `64`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-003 concretely specializes address widths without runtime XLEN selection")
step("Verify: REQ-G2-003 concretely specializes address widths without runtime XLEN selection")
val rv32 = strict_riscv_predecode_interface(CoreConfig.rv32_zca_mission_critical())
val rv64 = strict_riscv_predecode_interface(CoreConfig.rv64_zca_mission_critical())
if val interface32 = rv32.ok():
    expect(interface32.shape_diagnostic()).to_equal("")
    expect(interface32.original_parcel.bit_width).to_equal(16)
    expect(interface32.fetch_pc.bit_width).to_equal(32)
    expect(interface32.canonical_instruction.bit_width).to_equal(32)
    expect(interface32.original_length_bytes.bit_width).to_equal(2)
    expect(interface32.next_pc.bit_width).to_equal(32)
    expect(interface32.redirect_target.bit_width).to_equal(32)
else:
    expect(false).to_equal(true)
if val interface64 = rv64.ok():
    expect(interface64.fetch_pc.bit_width).to_equal(56)
    expect(interface64.next_pc.bit_width).to_equal(56)
    expect(interface64.redirect_target.bit_width).to_equal(56)
    expect(interface64.config.xlen).to_equal(64)
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-003 refuses non-critical and malformed predecode interfaces before emission

- REQ-G2-003 refuses non-critical and malformed predecode interfaces before emission
- Verify: REQ-G2-003 refuses non-critical and malformed predecode interfaces before emission
   - Expected: diagnostic equals `HWIR-E-PREDECODE-PROFILE: strict compressed predecode requires zca-common-cri... (full value in folded executable source)`
   - Expected: false is true
   - Expected: malformed.shape_diagnostic() equals `HWIR-E-PREDECODE-DIRECTION: parcel and fetch PC are inputs; all predecode res... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-003 refuses non-critical and malformed predecode interfaces before emission")
step("Verify: REQ-G2-003 refuses non-critical and malformed predecode interfaces before emission")
val base = strict_riscv_predecode_interface(CoreConfig.rv32())
expect(base.is_err()).to_be(true)
if val diagnostic = base.err():
    expect(diagnostic).to_equal("HWIR-E-PREDECODE-PROFILE: strict compressed predecode requires zca-common-critical profile")
else:
    expect(false).to_equal(true)
val config = CoreConfig.rv32_zca_mission_critical()
val malformed = HwPredecodeInterface(
    node_id: HwNodeId.module_root("riscv_predecode"), config: config,
    original_parcel: HwPort.output("original_parcel", "Bits", 16),
    fetch_pc: HwPort.input("fetch_pc", "Bits", 31),
    canonical_instruction: HwPort.output("canonical_instruction", "Bits", 32),
    original_length_bytes: HwPort.output("original_length_bytes", "Bits", 2),
    legal: HwPort.output("legal", "Bits", 1),
    next_pc: HwPort.output("next_pc", "Bits", 32),
    redirect_valid: HwPort.output("redirect_valid", "Bits", 1),
    redirect_target: HwPort.output("redirect_target", "Bits", 32)
)
expect(malformed.shape_diagnostic()).to_equal("HWIR-E-PREDECODE-DIRECTION: parcel and fetch PC are inputs; all predecode results are outputs")
```

</details>

#### REQ-G2-003 constructs C.J only as a typed predecode and redirect graph

- REQ-G2-003 constructs C.J only as a typed predecode and redirect graph
- Verify: REQ-G2-003 constructs C.J only as a typed predecode and redirect graph
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.port_width("original_parcel") equals `16`
   - Expected: module.port_width("canonical_instruction") equals `32`
   - Expected: module.port_width("fetch_pc") equals `56`
   - Expected: module.port_width("next_pc") equals `56`
   - Expected: module.port_width("redirect_target") equals `56`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-003 constructs C.J only as a typed predecode and redirect graph")
step("Verify: REQ-G2-003 constructs C.J only as a typed predecode and redirect graph")
val built = strict_zca_cj_predecode_row_hwir("strict_cj_predecode", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.port_width("original_parcel")).to_equal(16)
    expect(module.port_width("canonical_instruction")).to_equal(32)
    expect(module.port_width("fetch_pc")).to_equal(56)
    expect(module.port_width("next_pc")).to_equal(56)
    expect(module.port_width("redirect_target")).to_equal(56)
    expect(module.has_port("redirect_valid")).to_be(true)
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_be(true)
    expect(emitted.vhdl.contains("resize(signed(immediate_signed), 56)")).to_be(true)
    expect(emitted.vhdl.contains("unsigned(fetch_pc) + unsigned(immediate_pa)")).to_be(true)
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-003 rejects C.J predecode outside the frozen critical profile

- REQ-G2-003 rejects C.J predecode outside the frozen critical profile
- Verify: REQ-G2-003 rejects C.J predecode outside the frozen critical profile
   - Expected: diagnostic equals `HWIR-E-PREDECODE-PROFILE: strict compressed predecode requires zca-common-cri... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-003 rejects C.J predecode outside the frozen critical profile")
step("Verify: REQ-G2-003 rejects C.J predecode outside the frozen critical profile")
val rejected = strict_zca_cj_predecode_row_hwir("strict_cj_base", CoreConfig.rv32())
expect(rejected.is_err()).to_be(true)
if val diagnostic = rejected.err():
    expect(diagnostic).to_equal("HWIR-E-PREDECODE-PROFILE: strict compressed predecode requires zca-common-critical profile")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-003 specializes conditional-branch operand width with the product

- REQ-G2-003 specializes conditional-branch operand width with the product
- Verify: REQ-G2-003 specializes conditional-branch operand width with the product
   - Expected: interface32.shape_diagnostic() equals ``
   - Expected: interface32.rs1_index.bit_width equals `5`
   - Expected: interface32.rs1_value.bit_width equals `32`
   - Expected: interface32.ports().len() equals `10`
   - Expected: false is true
   - Expected: interface64.rs1_value.bit_width equals `64`
   - Expected: interface64.predecode.redirect_target.bit_width equals `56`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-003 specializes conditional-branch operand width with the product")
step("Verify: REQ-G2-003 specializes conditional-branch operand width with the product")
val rv32 = strict_riscv_branch_predecode_interface(CoreConfig.rv32_zca_mission_critical())
val rv64 = strict_riscv_branch_predecode_interface(CoreConfig.rv64_zca_mission_critical())
if val interface32 = rv32.ok():
    expect(interface32.shape_diagnostic()).to_equal("")
    expect(interface32.rs1_index.bit_width).to_equal(5)
    expect(interface32.rs1_value.bit_width).to_equal(32)
    expect(interface32.ports().len()).to_equal(10)
else:
    expect(false).to_equal(true)
if val interface64 = rv64.ok():
    expect(interface64.rs1_value.bit_width).to_equal(64)
    expect(interface64.predecode.redirect_target.bit_width).to_equal(56)
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-003 rejects a conditional branch operand that is not XLEN-wide Bits

- REQ-G2-003 rejects a conditional branch operand that is not XLEN-wide Bits
- Verify: REQ-G2-003 rejects a conditional branch operand that is not XLEN-wide Bits
   - Expected: malformed.shape_diagnostic() equals `HWIR-E-BRANCH-PREDECODE-OPERAND: conditional branch requires an XLEN-wide Bit... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-003 rejects a conditional branch operand that is not XLEN-wide Bits")
step("Verify: REQ-G2-003 rejects a conditional branch operand that is not XLEN-wide Bits")
val config = CoreConfig.rv32_zca_mission_critical()
val predecode = strict_riscv_predecode_interface(config)
if val base = predecode.ok():
    val malformed = HwBranchPredecodeInterface(
        node_id: HwNodeId.module_root("riscv_branch_predecode"), config: config,
        predecode: base, rs1_index: HwPort.input("rs1_index", "Bits", 5),
        rs1_value: HwPort.input("rs1_value", "Bits", 31)
    )
    expect(malformed.shape_diagnostic()).to_equal("HWIR-E-BRANCH-PREDECODE-OPERAND: conditional branch requires an XLEN-wide Bits rs1_value input")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-004 freezes a concrete frontend-to-dispatch handoff without claiming row composition

- REQ-G2-004 freezes a concrete frontend-to-dispatch handoff without claiming row composition
- Verify: REQ-G2-004 freezes a concrete frontend-to-dispatch handoff without claiming row composition
   - Expected: frontend32.shape_diagnostic() equals ``
   - Expected: frontend32.ports().len() equals `12`
   - Expected: frontend32.branch_predecode.predecode.original_parcel.name equals `original_parcel`
   - Expected: frontend32.branch_predecode.predecode.original_parcel.bit_width equals `16`
   - Expected: frontend32.branch_predecode.predecode.canonical_instruction.name equals `canonical_instruction`
   - Expected: frontend32.branch_predecode.predecode.canonical_instruction.bit_width equals `32`
   - Expected: frontend32.branch_predecode.predecode.original_length_bytes.bit_width equals `2`
   - Expected: frontend32.branch_predecode.predecode.legal.bit_width equals `1`
   - Expected: frontend32.branch_predecode.predecode.next_pc.bit_width equals `32`
   - Expected: frontend32.branch_predecode.predecode.redirect_target.bit_width equals `32`
   - Expected: frontend32.branch_predecode.rs1_index.name equals `rs1_index`
   - Expected: frontend32.branch_predecode.rs1_index.direction equals `in`
   - Expected: frontend32.branch_predecode.rs1_index.bit_width equals `5`
   - Expected: frontend32.branch_predecode.rs1_value.name equals `rs1_value`
   - Expected: frontend32.branch_predecode.rs1_value.direction equals `in`
   - Expected: frontend32.branch_predecode.rs1_value.bit_width equals `32`
   - Expected: frontend32.dispatch_accept.name equals `dispatch_accept`
   - Expected: frontend32.dispatch_accept.direction equals `in`
   - Expected: frontend32.dispatch_accept.bit_width equals `1`
   - Expected: frontend32.retire_valid.name equals `retire_valid`
   - Expected: frontend32.retire_valid.direction equals `out`
   - Expected: frontend32.retire_valid.bit_width equals `1`
   - Expected: false is true
   - Expected: frontend64.config.xlen equals `64`
   - Expected: frontend64.branch_predecode.rs1_value.bit_width equals `64`
   - Expected: frontend64.branch_predecode.predecode.fetch_pc.bit_width equals `56`
   - Expected: frontend64.branch_predecode.predecode.next_pc.bit_width equals `56`
   - Expected: frontend64.branch_predecode.predecode.redirect_target.bit_width equals `56`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-004 freezes a concrete frontend-to-dispatch handoff without claiming row composition")
step("Verify: REQ-G2-004 freezes a concrete frontend-to-dispatch handoff without claiming row composition")
val rv32 = strict_riscv_frontend_handoff_interface(CoreConfig.rv32_zca_mission_critical())
val rv64 = strict_riscv_frontend_handoff_interface(CoreConfig.rv64_zca_mission_critical())
if val frontend32 = rv32.ok():
    expect(frontend32.shape_diagnostic()).to_equal("")
    expect(frontend32.ports().len()).to_equal(12)
    expect(frontend32.branch_predecode.predecode.original_parcel.name).to_equal("original_parcel")
    expect(frontend32.branch_predecode.predecode.original_parcel.bit_width).to_equal(16)
    expect(frontend32.branch_predecode.predecode.canonical_instruction.name).to_equal("canonical_instruction")
    expect(frontend32.branch_predecode.predecode.canonical_instruction.bit_width).to_equal(32)
    expect(frontend32.branch_predecode.predecode.original_length_bytes.bit_width).to_equal(2)
    expect(frontend32.branch_predecode.predecode.legal.bit_width).to_equal(1)
    expect(frontend32.branch_predecode.predecode.next_pc.bit_width).to_equal(32)
    expect(frontend32.branch_predecode.predecode.redirect_target.bit_width).to_equal(32)
    expect(frontend32.branch_predecode.rs1_index.name).to_equal("rs1_index")
    expect(frontend32.branch_predecode.rs1_index.direction).to_equal("in")
    expect(frontend32.branch_predecode.rs1_index.bit_width).to_equal(5)
    expect(frontend32.branch_predecode.rs1_value.name).to_equal("rs1_value")
    expect(frontend32.branch_predecode.rs1_value.direction).to_equal("in")
    expect(frontend32.branch_predecode.rs1_value.bit_width).to_equal(32)
    expect(frontend32.dispatch_accept.name).to_equal("dispatch_accept")
    expect(frontend32.dispatch_accept.direction).to_equal("in")
    expect(frontend32.dispatch_accept.bit_width).to_equal(1)
    expect(frontend32.retire_valid.name).to_equal("retire_valid")
    expect(frontend32.retire_valid.direction).to_equal("out")
    expect(frontend32.retire_valid.bit_width).to_equal(1)
else:
    expect(false).to_equal(true)
if val frontend64 = rv64.ok():
    expect(frontend64.config.xlen).to_equal(64)
    expect(frontend64.branch_predecode.rs1_value.bit_width).to_equal(64)
    expect(frontend64.branch_predecode.predecode.fetch_pc.bit_width).to_equal(56)
    expect(frontend64.branch_predecode.predecode.next_pc.bit_width).to_equal(56)
    expect(frontend64.branch_predecode.predecode.redirect_target.bit_width).to_equal(56)
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-004 fails closed for a frontend configuration mismatch

- REQ-G2-004 fails closed for a frontend configuration mismatch
- Verify: REQ-G2-004 fails closed for a frontend configuration mismatch
   - Expected: mismatch.shape_diagnostic() equals `HWIR-E-FRONTEND-CONFIG: frontend and branch-predecode interfaces must use one... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-004 fails closed for a frontend configuration mismatch")
step("Verify: REQ-G2-004 fails closed for a frontend configuration mismatch")
val config = CoreConfig.rv32_zca_mission_critical()
val branch = strict_riscv_branch_predecode_interface(CoreConfig.rv64_zca_mission_critical())
if val branch64 = branch.ok():
    val mismatch = HwFrontendHandoffInterface(
        node_id: HwNodeId.module_root("riscv_gen2_frontend_handoff"), config: config,
        branch_predecode: branch64,
        dispatch_accept: HwPort.input("dispatch_accept", "Bits", 1),
        retire_valid: HwPort.output("retire_valid", "Bits", 1)
    )
    expect(mismatch.shape_diagnostic()).to_equal("HWIR-E-FRONTEND-CONFIG: frontend and branch-predecode interfaces must use one concrete product configuration")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-004 fails closed for malformed dispatch and retire ownership ports

- REQ-G2-004 fails closed for malformed dispatch and retire ownership ports
- Verify: REQ-G2-004 fails closed for malformed dispatch and retire ownership ports
   - Expected: malformed_dispatch.shape_diagnostic() equals `HWIR-E-FRONTEND-DISPATCH: frontend handoff requires a one-bit Bits dispatch_a... (full value in folded executable source)`
   - Expected: malformed_retire.shape_diagnostic() equals `HWIR-E-FRONTEND-RETIRE: frontend handoff requires a one-bit Bits retire_valid... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-004 fails closed for malformed dispatch and retire ownership ports")
step("Verify: REQ-G2-004 fails closed for malformed dispatch and retire ownership ports")
val config = CoreConfig.rv32_zca_mission_critical()
val branch = strict_riscv_branch_predecode_interface(config)
if val branch_contract = branch.ok():
    val malformed_dispatch = HwFrontendHandoffInterface(
        node_id: HwNodeId.module_root("riscv_gen2_frontend_handoff"), config: config,
        branch_predecode: branch_contract,
        dispatch_accept: HwPort.output("dispatch_accept", "Bits", 1),
        retire_valid: HwPort.output("retire_valid", "Bits", 1)
    )
    expect(malformed_dispatch.shape_diagnostic()).to_equal("HWIR-E-FRONTEND-DISPATCH: frontend handoff requires a one-bit Bits dispatch_accept input")
    val malformed_retire = HwFrontendHandoffInterface(
        node_id: HwNodeId.module_root("riscv_gen2_frontend_handoff"), config: config,
        branch_predecode: branch_contract,
        dispatch_accept: HwPort.input("dispatch_accept", "Bits", 1),
        retire_valid: HwPort.output("retire_valid", "Bits", 2)
    )
    expect(malformed_retire.shape_diagnostic()).to_equal("HWIR-E-FRONTEND-RETIRE: frontend handoff requires a one-bit Bits retire_valid output")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-003 constructs conditional rows with an explicit XLEN operand and typed branch direction

- REQ-G2-003 constructs conditional rows with an explicit XLEN operand and typed branch direction
- Verify: REQ-G2-003 constructs conditional rows with an explicit XLEN operand and typed branch direction
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.port_width("rs1_value") equals `32`
   - Expected: module.port_width("redirect_target") equals `32`
   - Expected: module.origins[0].source_name equals `zca.c.beqz`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-003 constructs conditional rows with an explicit XLEN operand and typed branch direction")
step("Verify: REQ-G2-003 constructs conditional rows with an explicit XLEN operand and typed branch direction")
val beqz = strict_zca_cbeqz_predecode_row_hwir("strict_cbeqz_predecode", CoreConfig.rv32_zca_mission_critical())
val bnez = strict_zca_cbnez_predecode_row_hwir("strict_cbnez_predecode", CoreConfig.rv64_zca_mission_critical())
if val module = beqz.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.port_width("rs1_value")).to_equal(32)
    expect(module.port_width("redirect_target")).to_equal(32)
    expect(module.origins[0].source_name).to_equal("zca.c.beqz")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_be(true)
    expect(emitted.vhdl.contains("rs1_value = zero_xlen")).to_be(true)
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-003 binds indirect compressed redirects to the decoded rs1 read pair

- REQ-G2-003 binds indirect compressed redirects to the decoded rs1 read pair
- Verify: REQ-G2-003 binds indirect compressed redirects to the decoded rs1 read pair
   - Expected: cjr.ok().unwrap().shape_diagnostic() equals ``
   - Expected: cjr.ok().unwrap().port_width("rs1_value") equals `32`
   - Expected: cjalr.ok().unwrap().shape_diagnostic() equals ``
   - Expected: cjalr.ok().unwrap().port_width("rs1_value") equals `64`
   - Expected: cjalr.ok().unwrap().port_width("redirect_target") equals `56`
   - Expected: false is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.port_width("rs1_value") equals `64`
   - Expected: module.port_width("redirect_target") equals `56`
   - Expected: module.origins[0].source_name equals `zca.c.bnez`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-003 binds indirect compressed redirects to the decoded rs1 read pair")
step("Verify: REQ-G2-003 binds indirect compressed redirects to the decoded rs1 read pair")
val cjr = strict_zca_cjr_predecode_row_hwir("strict_cjr_predecode", CoreConfig.rv32_zca_mission_critical())
val cjalr = strict_zca_cjalr_predecode_row_hwir("strict_cjalr_predecode", CoreConfig.rv64_zca_mission_critical())
if cjr.is_ok() and cjalr.is_ok():
    expect(cjr.ok().unwrap().shape_diagnostic()).to_equal("")
    expect(cjr.ok().unwrap().port_width("rs1_value")).to_equal(32)
    expect(cjalr.ok().unwrap().shape_diagnostic()).to_equal("")
    expect(cjalr.ok().unwrap().port_width("rs1_value")).to_equal(64)
    expect(cjalr.ok().unwrap().port_width("redirect_target")).to_equal(56)
else:
    expect(false).to_equal(true)
if val module = bnez.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.port_width("rs1_value")).to_equal(64)
    expect(module.port_width("redirect_target")).to_equal(56)
    expect(module.origins[0].source_name).to_equal("zca.c.bnez")
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-004 emits a flat critical C.J/C.BEQZ/C.BNEZ control-predecode composition

- REQ-G2-004 emits a flat critical C.J/C.BEQZ/C.BNEZ control-predecode composition
- Verify: REQ-G2-004 emits a flat critical C.J/C.BEQZ/C.BNEZ control-predecode composition
   - Expected: module32.shape_diagnostic() equals ``
   - Expected: module32.ports.len() equals `10`
   - Expected: module32.port_width("original_parcel") equals `16`
   - Expected: module32.port_width("fetch_pc") equals `32`
   - Expected: module32.port_width("rs1_index") equals `5`
   - Expected: module32.port_width("rs1_value") equals `32`
   - Expected: module32.port_width("canonical_instruction") equals `32`
   - Expected: module32.port_width("next_pc") equals `32`
   - Expected: module32.port_width("redirect_target") equals `32`
   - Expected: strict_output_driver_count(module32, output_name) equals `1`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `entity strict_zca_control_rv32 is`
   - Expected: false is true
   - Expected: module64.shape_diagnostic() equals ``
   - Expected: module64.ports.len() equals `10`
   - Expected: module64.port_width("rs1_value") equals `64`
   - Expected: module64.port_width("fetch_pc") equals `56`
   - Expected: module64.port_width("next_pc") equals `56`
   - Expected: module64.port_width("redirect_target") equals `56`
   - Expected: strict_output_driver_count(module64, output_name) equals `1`
   - Expected: render_strict_hwir_vhdl(module64).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-004 emits a flat critical C.J/C.BEQZ/C.BNEZ control-predecode composition")
step("Verify: REQ-G2-004 emits a flat critical C.J/C.BEQZ/C.BNEZ control-predecode composition")
val rv32 = strict_zca_control_predecode_hwir("strict_zca_control_rv32", CoreConfig.rv32_zca_mission_critical())
val rv64 = strict_zca_control_predecode_hwir("strict_zca_control_rv64", CoreConfig.rv64_zca_mission_critical())
if val module32 = rv32.ok():
    expect(module32.shape_diagnostic()).to_equal("")
    expect(module32.ports.len()).to_equal(10)
    expect(module32.port_width("original_parcel")).to_equal(16)
    expect(module32.port_width("fetch_pc")).to_equal(32)
    expect(module32.port_width("rs1_index")).to_equal(5)
    expect(module32.port_width("rs1_value")).to_equal(32)
    expect(module32.port_width("canonical_instruction")).to_equal(32)
    expect(module32.port_width("next_pc")).to_equal(32)
    expect(module32.port_width("redirect_target")).to_equal(32)
    expect(strict_origin_source_count(module32, "zca.c.j")).to_be_greater_than(0)
    expect(strict_origin_source_count(module32, "zca.c.beqz")).to_be_greater_than(0)
    expect(strict_origin_source_count(module32, "zca.c.bnez")).to_be_greater_than(0)
    for output_name in ["canonical_instruction", "original_length_bytes", "legal", "next_pc", "redirect_valid", "redirect_target"]:
        expect(strict_output_driver_count(module32, output_name)).to_equal(1)
    val emitted = render_strict_hwir_vhdl(module32)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("entity strict_zca_control_rv32 is")).to_equal(true)
else:
    expect(false).to_equal(true)
if val module64 = rv64.ok():
    expect(module64.shape_diagnostic()).to_equal("")
    expect(module64.ports.len()).to_equal(10)
    expect(module64.port_width("rs1_value")).to_equal(64)
    expect(module64.port_width("fetch_pc")).to_equal(56)
    expect(module64.port_width("next_pc")).to_equal(56)
    expect(module64.port_width("redirect_target")).to_equal(56)
    expect(strict_origin_source_count(module64, "zca.c.j")).to_be_greater_than(0)
    expect(strict_origin_source_count(module64, "zca.c.beqz")).to_be_greater_than(0)
    expect(strict_origin_source_count(module64, "zca.c.bnez")).to_be_greater_than(0)
    for output_name in ["canonical_instruction", "original_length_bytes", "legal", "next_pc", "redirect_valid", "redirect_target"]:
        expect(strict_output_driver_count(module64, output_name)).to_equal(1)
    expect(render_strict_hwir_vhdl(module64).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### REQ-G2-004 refuses control-predecode composition outside the critical compressed profile

- REQ-G2-004 refuses control-predecode composition outside the critical compressed profile
- Verify: REQ-G2-004 refuses control-predecode composition outside the critical compressed profile
   - Expected: rejected.is_err() is true
   - Expected: diagnostic equals `HWIR-E-PREDECODE-PROFILE: strict compressed predecode requires zca-common-cri... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-G2-004 refuses control-predecode composition outside the critical compressed profile")
step("Verify: REQ-G2-004 refuses control-predecode composition outside the critical compressed profile")
val rejected = strict_zca_control_predecode_hwir("strict_zca_control_base", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
if val diagnostic = rejected.err():
    expect(diagnostic).to_equal("HWIR-E-PREDECODE-PROFILE: strict compressed predecode requires zca-common-critical profile")
else:
    expect(false).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-G2-001`
- `REQ-G2-011`
- `REQ-G2-002/003`
- `REQ-G2-010`
- `REQ-G2-003`
- `REQ-G2-002`
- `REQ-G2-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `157bb5d40f1ddb14eb4b05c50464a8d281279684628db54daac504de2dc93f54`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `157bb5d40f1ddb14eb4b05c50464a8d281279684628db54daac504de2dc93f54`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `157bb5d40f1ddb14eb4b05c50464a8d281279684628db54daac504de2dc93f54`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/compiler/50.mir/hwir_predecode_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_predecode_contract_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_predecode_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_predecode_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_predecode_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 108 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_predecode_contract_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-G2-001 rejects duplicate strict-HWIR drivers before emission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_predecode_contract_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-G2-011 isolates RV32 C.JAL from the common profile and preserves its x1 link field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_predecode_contract_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-G2-011 composes C.JAL only into a distinct RV32 migrating frontend product' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_predecode_contract_spec.spl:303:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should close each specialized trap decoder over exactly one target row and C.EBREAK' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_predecode_contract_spec.spl:341:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind each specialized trap frontend and decoder to one closed no-overlap graph' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
