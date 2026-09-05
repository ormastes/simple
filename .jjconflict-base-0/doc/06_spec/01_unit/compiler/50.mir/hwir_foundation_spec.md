# Hwir Foundation Specification

> Tests covering RISC-V Gen2 strict HWIR foundation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 50 | 50 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Foundation Specification

## Scenarios

### RISC-V Gen2 strict HWIR foundation

#### should construct stable typed origins and concrete ports

- should construct stable typed origins and concrete ports
- Lower the canonical RV32 typed module and inspect its origins and ports
   - Expected: module.node_id.value equals `gen2_and:module`
   - Expected: module.origins[0].node_id.value equals `gen2_and:and`
   - Expected: module.ports.len() equals `3`
   - Expected: module.shape_diagnostic() equals ``
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct stable typed origins and concrete ports")
step("Lower the canonical RV32 typed module and inspect its origins and ports")
val result = strict_rv32_result()
check(result.is_success())
if val module = result.module:
    expect(module.node_id.value).to_equal("gen2_and:module")
    expect(module.origins[0].node_id.value).to_equal("gen2_and:and")
    expect(module.ports.len()).to_equal(3)
    expect(module.shape_diagnostic()).to_equal("")
else:
    expect(false).to_equal(true)
```

</details>

#### should bind strict artifact provenance to the canonical typed graph

- should bind strict artifact provenance to the canonical typed graph
- Lower the same typed graph twice and mutate one operation for identity comparison
   - Expected: first_module.structural_sha256().len() equals `64`
   - Expected: first_module.structural_sha256() equals `second_module.structural_sha256()`
   - Expected: first_module.structural_sha256() == second_module.structural_sha256() is false
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should bind strict artifact provenance to the canonical typed graph")
step("Lower the same typed graph twice and mutate one operation for identity comparison")
val first = strict_rv32_result()
val second = strict_rv32_result()
if val first_module = first.module:
    if val second_module = second.module:
        expect(first_module.structural_sha256().len()).to_equal(64)
        expect(first_module.structural_sha256()).to_equal(second_module.structural_sha256())
        val mutated_op = second_module.comb_ops[0]
        mutated_op.op = "or"
        second_module.comb_ops[0] = mutated_op
        expect(first_module.structural_sha256() == second_module.structural_sha256()).to_equal(false)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should use length-prefixed graph fields to prevent delimiter hash ambiguity

- should use length-prefixed graph fields to prevent delimiter hash ambiguity
- Hash two delimiter-bearing graph-field sequences with distinct boundaries
   - Expected: hwir_hash_fields(["origin", "a|b", "c"]) == hwir_hash_fields(["origin", "a", "b|c"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should use length-prefixed graph fields to prevent delimiter hash ambiguity")
step("Hash two delimiter-bearing graph-field sequences with distinct boundaries")
expect(hwir_hash_fields(["origin", "a|b", "c"]) == hwir_hash_fields(["origin", "a", "b|c"])).to_equal(false)
```

</details>

#### should bind delimiter-bearing origin lineage without graph-hash aliasing

- should bind delimiter-bearing origin lineage without graph-hash aliasing
- Assign distinct delimiter-bearing origin fields to two typed graphs
   - Expected: first_module.shape_diagnostic() equals ``
   - Expected: second_module.shape_diagnostic() equals ``
   - Expected: first_module.structural_sha256() == second_module.structural_sha256() is false
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should bind delimiter-bearing origin lineage without graph-hash aliasing")
step("Assign distinct delimiter-bearing origin fields to two typed graphs")
val first = strict_rv32_result()
val second = strict_rv32_result()
if val first_module = first.module:
    if val second_module = second.module:
        val first_origin = first_module.origins[0]
        first_origin.node_id.value = "origin|part"
        first_origin.source_name = "tail"
        first_module.origins[0] = first_origin
        val second_origin = second_module.origins[0]
        second_origin.node_id.value = "origin"
        second_origin.source_name = "part|tail"
        second_module.origins[0] = second_origin
        expect(first_module.shape_diagnostic()).to_equal("")
        expect(second_module.shape_diagnostic()).to_equal("")
        expect(first_module.structural_sha256() == second_module.structural_sha256()).to_equal(false)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should specialize RV32 and RV64 at elaboration time

- should specialize RV32 and RV64 at elaboration time
- Lower concrete RV32 and RV64 configurations and inspect their selected widths
   - Expected: module32.ports[0].bit_width equals `32`
   - Expected: false is true
   - Expected: module64.ports[0].bit_width equals `64`
   - Expected: module64.config.xlen equals `64`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should specialize RV32 and RV64 at elaboration time")
step("Lower concrete RV32 and RV64 configurations and inspect their selected widths")
val rv32 = strict_rv32_result()
val rv64 = lower_strict_hwir_and_module(HwirLowerInput.hardware("gen2_and64", 2, 1, 0, 0), CoreConfig.rv64())
if val module32 = rv32.module:
    expect(module32.ports[0].bit_width).to_equal(32)
else:
    expect(false).to_equal(true)
if val module64 = rv64.module:
    expect(module64.ports[0].bit_width).to_equal(64)
    expect(module64.config.xlen).to_equal(64)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject invalid elaboration configuration

- should reject invalid elaboration configuration
- Submit an invalid XLEN configuration to strict HWIR lowering
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-CONFIG-XLEN: strict RISC-V HWIR requires XLEN=32 or XLEN=64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject invalid elaboration configuration")
step("Submit an invalid XLEN configuration to strict HWIR lowering")
val invalid = CoreConfig(xlen: 16, physical_address_bits: 0, register_count: 0,
    profile: "", isa_profile: "", compressed_decode_profile: "")
val result = lower_strict_hwir_and_module(HwirLowerInput.hardware("bad", 2, 1, 0, 0), invalid)
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-CONFIG-XLEN: strict RISC-V HWIR requires XLEN=32 or XLEN=64")
```

</details>

#### should fail closed before a profile can escape strict VHDL provenance

- should fail closed before a profile can escape strict VHDL provenance
- Submit a line-control profile name before strict HWIR lowering
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-CONFIG-PROFILE: strict RISC-V HWIR requires safe concrete profile names`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should fail closed before a profile can escape strict VHDL provenance")
step("Submit a line-control profile name before strict HWIR lowering")
val injected = CoreConfig(xlen: 32, physical_address_bits: 32, register_count: 32,
    profile: "rv32\nend architecture;", isa_profile: "rv32i", compressed_decode_profile: "none")
val result = lower_strict_hwir_and_module(HwirLowerInput.hardware("unsafe_profile", 2, 1, 0, 0), injected)
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-CONFIG-PROFILE: strict RISC-V HWIR requires safe concrete profile names")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject nested VHDL comment delimiters in strict profile tokens

- should reject nested VHDL comment delimiters in strict profile tokens
- Submit a comment-bearing profile token to the concrete configuration boundary
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-CONFIG-PROFILE: strict RISC-V HWIR requires safe concrete profile names`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject nested VHDL comment delimiters in strict profile tokens")
step("Submit a comment-bearing profile token to the concrete configuration boundary")
val injected = CoreConfig(xlen: 32, physical_address_bits: 32, register_count: 32,
    profile: "rv32--forged-provenance", isa_profile: "rv32i", compressed_decode_profile: "none")
val result = lower_strict_hwir_and_module(HwirLowerInput.hardware("unsafe_comment_profile", 2, 1, 0, 0), injected)
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-CONFIG-PROFILE: strict RISC-V HWIR requires safe concrete profile names")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject VHDL reserved words before strict text emission

- should reject VHDL reserved words before strict text emission
- Replace the typed module name with a VHDL reserved word
   - Expected: module.shape_diagnostic() equals `HWIR-E-VHDL-IDENTIFIER: module name is not a stable VHDL identifier`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject VHDL reserved words before strict text emission")
step("Replace the typed module name with a VHDL reserved word")
val result = strict_rv32_result()
if val module = result.module:
    module.summary.name = "entity"
    expect(module.shape_diagnostic()).to_equal("HWIR-E-VHDL-IDENTIFIER: module name is not a stable VHDL identifier")
else:
    expect(false).to_equal(true)
```

</details>

#### should reject VHDL reserved port names before strict text emission

- should reject VHDL reserved port names before strict text emission
- Replace a typed port name with a VHDL reserved word
   - Expected: module.shape_diagnostic() equals `HWIR-E-PORT: ports must be unique typed Bits in an existing clock domain`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject VHDL reserved port names before strict text emission")
step("Replace a typed port name with a VHDL reserved word")
val result = strict_rv32_result()
if val module = result.module:
    val reserved_port = module.ports[0]
    reserved_port.name = "signal"
    module.ports[0] = reserved_port
    expect(module.shape_diagnostic()).to_equal("HWIR-E-PORT: ports must be unique typed Bits in an existing clock domain")
else:
    expect(false).to_equal(true)
```

</details>

#### should reject case-only VHDL declaration collisions while preserving stored spellings

- should reject case-only VHDL declaration collisions while preserving stored spellings
- Create case-only port, signal, and constant declaration collisions
   - Expected: port_collision.shape_diagnostic() equals `HWIR-E-PORT: ports must be unique typed Bits in an existing clock domain`
   - Expected: signal_collision.shape_diagnostic() equals `HWIR-E-SIGNAL: signals must be unique positive-width Bits`
   - Expected: constant_collision.shape_diagnostic() equals `HWIR-E-CONSTANT: constants must be unique and positive-width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject case-only VHDL declaration collisions while preserving stored spellings")
step("Create case-only port, signal, and constant declaration collisions")
val port_collision = casefold_collision_module()
val collide_port = port_collision.ports[1]
collide_port.name = "PARCEL"
port_collision.ports[1] = collide_port
expect(port_collision.shape_diagnostic()).to_equal("HWIR-E-PORT: ports must be unique typed Bits in an existing clock domain")

val signal_collision = casefold_collision_module()
signal_collision.summary.signal_count = 1
signal_collision.signals = [HwSignal.comb("PARCEL", "Bits", 1)]
expect(signal_collision.shape_diagnostic()).to_equal("HWIR-E-SIGNAL: signals must be unique positive-width Bits")

val constant_collision = casefold_collision_module()
val collide_const = constant_collision.constants[0]
collide_const.name = "PARCEL"
constant_collision.constants[0] = collide_const
expect(constant_collision.shape_diagnostic()).to_equal("HWIR-E-CONSTANT: constants must be unique and positive-width")
```

</details>

#### should select compressed capability profiles at elaboration time

- should select compressed capability profiles at elaboration time
- Construct valid and mismatched compressed and ISA profile configurations
   - Expected: rv32.is_valid() is true
   - Expected: rv64.is_valid() is true
   - Expected: rv32.compressed_decode_profile equals `zca-integer-rv32`
   - Expected: rv64.compressed_decode_profile equals `zca-integer-rv64`
   - Expected: critical32.compressed_decode_profile equals `zca-common-critical`
   - Expected: critical64.compressed_decode_profile equals `zca-common-critical`
   - Expected: wrong.diagnostic() equals `HWIR-E-CONFIG-COMPRESSED: RV64 compressed profile requires XLEN=64`
   - Expected: mismatched_isa.diagnostic() equals `HWIR-E-CONFIG-ISA: RV64 scalar ISA profile requires XLEN=64`
   - Expected: unknown_isa.diagnostic() equals `HWIR-E-CONFIG-ISA: unsupported strict scalar ISA profile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should select compressed capability profiles at elaboration time")
step("Construct valid and mismatched compressed and ISA profile configurations")
val rv32 = CoreConfig.rv32_zca_integer()
val rv64 = CoreConfig.rv64_zca_integer()
val critical32 = CoreConfig.rv32_zca_mission_critical()
val critical64 = CoreConfig.rv64_zca_mission_critical()
expect(rv32.is_valid()).to_equal(true)
expect(rv64.is_valid()).to_equal(true)
expect(rv32.compressed_decode_profile).to_equal("zca-integer-rv32")
expect(rv64.compressed_decode_profile).to_equal("zca-integer-rv64")
expect(critical32.compressed_decode_profile).to_equal("zca-common-critical")
expect(critical64.compressed_decode_profile).to_equal("zca-common-critical")
val wrong = CoreConfig(xlen: 32, physical_address_bits: 32, register_count: 32,
    profile: "bad", isa_profile: "rv32i_zca",
    compressed_decode_profile: "zca-integer-rv64")
expect(wrong.diagnostic()).to_equal("HWIR-E-CONFIG-COMPRESSED: RV64 compressed profile requires XLEN=64")
val mismatched_isa = CoreConfig(xlen: 32, physical_address_bits: 32, register_count: 32,
    profile: "bad", isa_profile: "rv64i", compressed_decode_profile: "none")
expect(mismatched_isa.diagnostic()).to_equal("HWIR-E-CONFIG-ISA: RV64 scalar ISA profile requires XLEN=64")
val unknown_isa = CoreConfig(xlen: 32, physical_address_bits: 32, register_count: 32,
    profile: "bad", isa_profile: "rv32imafdc", compressed_decode_profile: "none")
expect(unknown_isa.diagnostic()).to_equal("HWIR-E-CONFIG-ISA: unsupported strict scalar ISA profile")
```

</details>

#### should use one closed mapping for mission-critical product targets

- should use one closed mapping for mission-critical product targets
- Resolve admitted and rejected mission-critical target identifiers
   - Expected: CoreConfig.is_supported_critical_target("rv32-zca-critical") is true
   - Expected: CoreConfig.is_supported_critical_target("rv64-zca-critical") is true
   - Expected: CoreConfig.is_supported_critical_target("rv64-zca") is false
   - Expected: config.xlen equals `32`
   - Expected: config.compressed_decode_profile equals `zca-common-critical`
   - Expected: false is true
   - Expected: rejected.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should use one closed mapping for mission-critical product targets")
step("Resolve admitted and rejected mission-critical target identifiers")
expect(CoreConfig.is_supported_critical_target("rv32-zca-critical")).to_equal(true)
expect(CoreConfig.is_supported_critical_target("rv64-zca-critical")).to_equal(true)
expect(CoreConfig.is_supported_critical_target("rv64-zca")).to_equal(false)
val resolved = CoreConfig.from_critical_target("rv32-zca-critical")
if val config = resolved.ok():
    expect(config.xlen).to_equal(32)
    expect(config.compressed_decode_profile).to_equal("zca-common-critical")
else:
    expect(false).to_equal(true)
val rejected = CoreConfig.from_critical_target("rv128")
expect(rejected.is_err()).to_equal(true)
```

</details>

#### should reject non-hardware and unsupported strict shapes without fallback

- should reject non-hardware and unsupported strict shapes without fallback
- Lower software-tagged and unsupported hardware shapes through the strict boundary
   - Expected: software.diagnostic equals `HWIR-E-NOT-HARDWARE: strict lowering requires a hardware-tagged input`
   - Expected: wrong_shape.diagnostic equals `HWIR-E-STRICT-SHAPE: strict Gen2 bridge currently requires two inputs, one ou... (full value in folded executable source)`
   - Expected: software.uses_legacy_fallback() is false
   - Expected: wrong_shape.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject non-hardware and unsupported strict shapes without fallback")
step("Lower software-tagged and unsupported hardware shapes through the strict boundary")
val software = lower_strict_hwir_and_module(HwirLowerInput.software("software"), CoreConfig.rv32())
val wrong_shape = lower_strict_hwir_and_module(HwirLowerInput.hardware("wrong", 1, 1, 0, 0), CoreConfig.rv32())
expect(software.diagnostic).to_equal("HWIR-E-NOT-HARDWARE: strict lowering requires a hardware-tagged input")
expect(wrong_shape.diagnostic).to_equal("HWIR-E-STRICT-SHAPE: strict Gen2 bridge currently requires two inputs, one output, and no local state")
expect(software.uses_legacy_fallback()).to_equal(false)
expect(wrong_shape.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should emit deterministic non-empty VHDL for the typed and module

- should emit deterministic non-empty VHDL for the typed and module
- Render the canonical typed module twice through the strict VHDL owner
   - Expected: first.vhdl equals `second.vhdl`
   - Expected: first.uses_legacy_fallback() is false
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should emit deterministic non-empty VHDL for the typed and module")
step("Render the canonical typed module twice through the strict VHDL owner")
val lower = strict_rv32_result()
if val module = lower.module:
    val first = render_strict_hwir_vhdl(module)
    val second = render_strict_hwir_vhdl(module)
    check(first.is_success())
    expect(first.vhdl).to_equal(second.vhdl)
    check(first.vhdl.contains("entity gen2_and is"))
    check(first.vhdl.contains("in_a : in std_logic_vector(31 downto 0)"))
    check(first.vhdl.contains("out <= in_a and in_b;"))
    expect(first.uses_legacy_fallback()).to_equal(false)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject malformed typed modules before emission

- should reject malformed typed modules before emission
- Render a typed module with an invalid port before strict emission
   - Expected: emitted.is_success() is false
   - Expected: emitted.diagnostic equals `HWIR-E-PORT: ports must be unique typed Bits in an existing clock domain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject malformed typed modules before emission")
step("Render a typed module with an invalid port before strict emission")
val summary = HwModule(name: "bad_port", profile: "rv32", port_count: 1, signal_count: 0, register_count: 0, memory_count: 0, comb_op_count: 0, clock_domain_count: 1, fallback_function: "", cost: HwCostModel.empty())
val malformed = HwModuleDef(summary: summary, config: CoreConfig.rv32(), node_id: HwNodeId.module_root("bad_port"), origins: [HwOrigin(node_id: HwNodeId.child("bad_port", "root"), source_name: "bad_port")], ports: [HwPort.input("", "Bits", 0)], signals: [], constants: [], comb_ops: [], compare_ops: [], select_ops: [], clock_domains: [HwClockDomain.default_domain()])
val emitted = render_strict_hwir_vhdl(malformed)
expect(emitted.is_success()).to_equal(false)
expect(emitted.diagnostic).to_equal("HWIR-E-PORT: ports must be unique typed Bits in an existing clock domain")
```

</details>

#### should fail closed when a stateful product leaves a public output unbound

- should fail closed when a stateful product leaves a public output unbound
- Remove one public output binding from the typed stateful frontend
   - Expected: frontend.shape_diagnostic() equals `HWIR-E-SEQUENTIAL-OUTPUT: every public output requires exactly one typed binding`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should fail closed when a stateful product leaves a public output unbound")
step("Remove one public output binding from the typed stateful frontend")
val built = strict_zca_single_outstanding_frontend_hwir("strict_stateful_unbound", CoreConfig.rv32_zca_mission_critical())
if val frontend = built.ok():
    var retained = []
    for output in frontend.sequential.outputs:
        if output.result != "protocol_fault":
            retained.push(output)
    frontend.sequential.outputs = retained
    expect(frontend.shape_diagnostic()).to_equal("HWIR-E-SEQUENTIAL-OUTPUT: every public output requires exactly one typed binding")
else:
    expect(false).to_equal(true)
```

</details>

#### should emit stable sequential HWIR lineage anchors with the stateful product

- should emit stable sequential HWIR lineage anchors with the stateful product
- Compile the typed stateful frontend and inspect sequential lineage markers
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `"graph=" + emitted.hwir_graph_sha256`
   - Expected: emitted.vhdl contains `-- simple-hwir node=riscv_gen2_zca_single_outstanding_frontend_rv32:sequentia... (full value in folded executable source)`
   - Expected: emitted.vhdl contains `-- simple-hwir node=riscv_gen2_zca_single_outstanding_frontend_rv32:sequentia... (full value in folded executable source)`
   - Expected: emitted.vhdl contains `-- simple-hwir node=riscv_gen2_zca_single_outstanding_frontend_rv32:sequentia... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should emit stable sequential HWIR lineage anchors with the stateful product")
step("Compile the typed stateful frontend and inspect sequential lineage markers")
val emitted = compile_strict_zca_single_outstanding_frontend_product(CoreConfig.rv32_zca_mission_critical())
expect(emitted.is_success()).to_equal(true)
expect(emitted.vhdl.contains("graph=" + emitted.hwir_graph_sha256)).to_equal(true)
expect(emitted.vhdl.contains("-- simple-hwir node=riscv_gen2_zca_single_outstanding_frontend_rv32:sequential:register:valid_reg")).to_equal(true)
expect(emitted.vhdl.contains("-- simple-hwir node=riscv_gen2_zca_single_outstanding_frontend_rv32:sequential:rule:retire_match")).to_equal(true)
expect(emitted.vhdl.contains("-- simple-hwir node=riscv_gen2_zca_single_outstanding_frontend_rv32:sequential:output:dispatch_valid")).to_equal(true)
```

</details>

#### should fail closed when the fixed frontend decoder pin map is altered

- should fail closed when the fixed frontend decoder pin map is altered
- Alter one selected frontend decoder pin before typed-plan validation
   - Expected: frontend.shape_diagnostic() equals `HWIR-E-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE: frontend sequential plan must exa... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should fail closed when the fixed frontend decoder pin map is altered")
step("Alter one selected frontend decoder pin before typed-plan validation")
val built = strict_zca_single_outstanding_frontend_hwir("strict_stateful_pins", CoreConfig.rv64_zca_mission_critical())
if val frontend = built.ok():
    val pin0 = frontend.sequential.decoder_pins[0]
    pin0.signal_name = "fetch_parcel"
    frontend.sequential.decoder_pins[0] = pin0
    expect(frontend.shape_diagnostic()).to_equal("HWIR-E-PARCEL-FRONTEND-SEQUENTIAL-TEMPLATE: frontend sequential plan must exactly match the selected fixed critical product")
else:
    expect(false).to_equal(true)
```

</details>

#### should reject line-control injection through sequential provenance IDs

- should reject line-control injection through sequential provenance IDs
- Inject a line-control character into the sequential owner identity
   - Expected: frontend.shape_diagnostic() equals `HWIR-E-SEQUENTIAL-ID: sequential plan requires a stable owner node ID`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject line-control injection through sequential provenance IDs")
step("Inject a line-control character into the sequential owner identity")
val built = strict_zca_single_outstanding_frontend_hwir("strict_stateful_id", CoreConfig.rv32_zca_mission_critical())
if val frontend = built.ok():
    frontend.sequential.owner_id.value = "safe:sequential\nunsafe"
    expect(frontend.shape_diagnostic()).to_equal("HWIR-E-SEQUENTIAL-ID: sequential plan requires a stable owner node ID")
else:
    expect(false).to_equal(true)
```

</details>

#### should reject serializer-unsafe identifiers before strict VHDL emission

- should reject serializer-unsafe identifiers before strict VHDL emission
- Construct a typed module whose entity identifier requires sanitization
   - Expected: render_strict_hwir_vhdl(malformed).diagnostic equals `HWIR-E-VHDL-IDENTIFIER: module name is not a stable VHDL identifier`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject serializer-unsafe identifiers before strict VHDL emission")
step("Construct a typed module whose entity identifier requires sanitization")
val summary = HwModule(name: "bad-module", profile: "rv32", port_count: 0,
    signal_count: 0, register_count: 0, memory_count: 0, comb_op_count: 0,
    clock_domain_count: 1, fallback_function: "", cost: HwCostModel.empty())
val malformed = HwModuleDef(summary: summary, config: CoreConfig.rv32(),
    node_id: HwNodeId.module_root("bad-module"),
    origins: [HwOrigin(node_id: HwNodeId.child("bad-module", "root"), source_name: "bad_module")],
    ports: [], signals: [], constants: [], comb_ops: [], compare_ops: [], select_ops: [],
    clock_domains: [HwClockDomain.default_domain()])
expect(render_strict_hwir_vhdl(malformed).diagnostic).to_equal("HWIR-E-VHDL-IDENTIFIER: module name is not a stable VHDL identifier")
```

</details>

#### should represent a typed fixed-width mask constant without VHDL text operands

- should represent a typed fixed-width mask constant without VHDL text operands
- Construct and render a typed fixed-width parcel-mask constant graph
   - Expected: module.shape_diagnostic() equals ``
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `constant parcel_mask_bits : std_logic_vector(31 downto 0) := "000000000000000... (full value in folded executable source)`
   - Expected: emitted.vhdl contains `masked <= parcel and parcel_mask_bits;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should represent a typed fixed-width mask constant without VHDL text operands")
step("Construct and render a typed fixed-width parcel-mask constant graph")
val summary = HwModule(name: "parcel_mask", profile: "rv32-zca", port_count: 2,
    signal_count: 0, register_count: 0, memory_count: 0, comb_op_count: 1,
    clock_domain_count: 1, fallback_function: "", cost: HwCostModel.empty())
val module = HwModuleDef(summary: summary, config: CoreConfig.rv32_zca_integer(),
    node_id: HwNodeId.module_root("parcel_mask"),
    origins: [HwOrigin(node_id: HwNodeId.child("parcel_mask", "mask"), source_name: "parcel_mask")],
    ports: [HwPort.input("parcel", "Bits", 32), HwPort.output("masked", "Bits", 32)],
    signals: [], constants: [HwConstant.bits("parcel_mask_bits", 32, 65535)],
    comb_ops: [HwCombOp.binary("and", "masked", "parcel", "parcel_mask_bits", 32)],
    compare_ops: [], select_ops: [],
    clock_domains: [HwClockDomain.default_domain()])
expect(module.shape_diagnostic()).to_equal("")
val emitted = render_strict_hwir_vhdl(module)
expect(emitted.is_success()).to_equal(true)
expect(emitted.vhdl.contains("constant parcel_mask_bits : std_logic_vector(31 downto 0) := \"00000000000000001111111111111111\";")).to_equal(true)
expect(emitted.vhdl.contains("masked <= parcel and parcel_mask_bits;")).to_equal(true)
```

</details>

#### should reject Zca semantic origins outside the critical profile

- should reject Zca semantic origins outside the critical profile
- Construct a Zca-semantic origin under a non-critical typed profile
   - Expected: module.shape_diagnostic() equals `HWIR-E-COMPRESSED-PROFILE: zca semantic origins require zca-common-critical p... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject Zca semantic origins outside the critical profile")
step("Construct a Zca-semantic origin under a non-critical typed profile")
val summary = HwModule(name: "bad_zca_profile", profile: "rv32", port_count: 0,
    signal_count: 0, register_count: 0, memory_count: 0, comb_op_count: 0,
    clock_domain_count: 1, fallback_function: "", cost: HwCostModel.empty())
val module = HwModuleDef(summary: summary, config: CoreConfig.rv32(),
    node_id: HwNodeId.module_root("bad_zca_profile"),
    origins: [HwOrigin(node_id: HwNodeId.child("bad_zca_profile", "row"), source_name: "zca.c.li")],
    ports: [], signals: [], constants: [], comb_ops: [], compare_ops: [], select_ops: [],
    clock_domains: [HwClockDomain.default_domain()])
expect(module.shape_diagnostic()).to_equal("HWIR-E-COMPRESSED-PROFILE: zca semantic origins require zca-common-critical profile")
```

</details>

#### should construct the compiler-owned C.LI row only for a critical product

- should construct the compiler-owned C.LI row only for a critical product
- Build the C.LI semantic row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.li`
   - Expected: module.summary.comb_op_count equals `18`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct the compiler-owned C.LI row only for a critical product")
step("Build the C.LI semantic row under rejected and admitted critical profiles")
val rejected = strict_zca_cli_row_hwir("strict_cli", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_cli_row_hwir("strict_cli", CoreConfig.rv32_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.li")
    expect(module.summary.comb_op_count).to_equal(18)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct the compiler-owned C.EBREAK row only for a critical product

- should construct the compiler-owned C.EBREAK row only for a critical product
- Build the C.EBREAK semantic row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.ebreak`
   - Expected: module.config.xlen equals `64`
   - Expected: module.select_ops[0].when_true equals `canonical_ebreak`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct the compiler-owned C.EBREAK row only for a critical product")
step("Build the C.EBREAK semantic row under rejected and admitted critical profiles")
val rejected = strict_zca_cebreak_row_hwir("strict_cebreak", CoreConfig.rv64())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_cebreak_row_hwir("strict_cebreak", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.ebreak")
    expect(module.config.xlen).to_equal(64)
    expect(module.select_ops[0].when_true).to_equal("canonical_ebreak")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct the compiler-owned C.ADDI4SPN row only for a critical product

- should construct the compiler-owned C.ADDI4SPN row only for a critical product
- Build the C.ADDI4SPN semantic row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.addi4spn`
   - Expected: module.summary.comb_op_count equals `29`
   - Expected: module.select_ops[1].condition equals `is_c_addi4spn`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct the compiler-owned C.ADDI4SPN row only for a critical product")
step("Build the C.ADDI4SPN semantic row under rejected and admitted critical profiles")
val rejected = strict_zca_addi4spn_row_hwir("strict_addi4spn", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_addi4spn_row_hwir("strict_addi4spn", CoreConfig.rv32_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.addi4spn")
    expect(module.summary.comb_op_count).to_equal(29)
    expect(module.select_ops[1].condition).to_equal("is_c_addi4spn")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct the compiler-owned C.LW row only for a critical product

- should construct the compiler-owned C.LW row only for a critical product
- Build the C.LW semantic row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.lw`
   - Expected: module.config.xlen equals `64`
   - Expected: module.summary.comb_op_count equals `28`
   - Expected: module.select_ops[0].condition equals `is_c_lw`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct the compiler-owned C.LW row only for a critical product")
step("Build the C.LW semantic row under rejected and admitted critical profiles")
val rejected = strict_zca_lw_row_hwir("strict_lw", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_lw_row_hwir("strict_lw", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.lw")
    expect(module.config.xlen).to_equal(64)
    expect(module.summary.comb_op_count).to_equal(28)
    expect(module.select_ops[0].condition).to_equal("is_c_lw")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct the compiler-owned C.SW row only for a critical product

- should construct the compiler-owned C.SW row only for a critical product
- Build the C.SW semantic row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.sw`
   - Expected: module.config.xlen equals `64`
   - Expected: module.summary.comb_op_count equals `32`
   - Expected: module.select_ops[0].condition equals `is_c_sw`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct the compiler-owned C.SW row only for a critical product")
step("Build the C.SW semantic row under rejected and admitted critical profiles")
val rejected = strict_zca_sw_row_hwir("strict_sw", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_sw_row_hwir("strict_sw", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.sw")
    expect(module.config.xlen).to_equal(64)
    expect(module.summary.comb_op_count).to_equal(32)
    expect(module.select_ops[0].condition).to_equal("is_c_sw")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct the compiler-owned C.LWSP row only for a critical product

- should construct the compiler-owned C.LWSP row only for a critical product
- Build the C.LWSP semantic row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.lwsp`
   - Expected: module.config.xlen equals `64`
   - Expected: module.summary.comb_op_count equals `26`
   - Expected: module.select_ops[1].condition equals `is_c_lwsp`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct the compiler-owned C.LWSP row only for a critical product")
step("Build the C.LWSP semantic row under rejected and admitted critical profiles")
val rejected = strict_zca_lwsp_row_hwir("strict_lwsp", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_lwsp_row_hwir("strict_lwsp", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.lwsp")
    expect(module.config.xlen).to_equal(64)
    expect(module.summary.comb_op_count).to_equal(26)
    expect(module.select_ops[1].condition).to_equal("is_c_lwsp")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct the compiler-owned C.SWSP row only for a critical product

- should construct the compiler-owned C.SWSP row only for a critical product
- Build the C.SWSP semantic row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.swsp`
   - Expected: module.config.xlen equals `64`
   - Expected: module.summary.comb_op_count equals `23`
   - Expected: module.select_ops[0].condition equals `is_c_swsp`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct the compiler-owned C.SWSP row only for a critical product")
step("Build the C.SWSP semantic row under rejected and admitted critical profiles")
val rejected = strict_zca_swsp_row_hwir("strict_swsp", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_swsp_row_hwir("strict_swsp", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.swsp")
    expect(module.config.xlen).to_equal(64)
    expect(module.summary.comb_op_count).to_equal(23)
    expect(module.select_ops[0].condition).to_equal("is_c_swsp")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct the five-bit C.SLLI row only for a critical product

- should construct the five-bit C.SLLI row only for a critical product
- Build the five-bit C.SLLI semantic row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.slli.low`
   - Expected: module.summary.comb_op_count equals `15`
   - Expected: module.select_ops[0].condition equals `is_c_slli_low`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct the five-bit C.SLLI row only for a critical product")
step("Build the five-bit C.SLLI semantic row under rejected and admitted critical profiles")
val rejected = strict_zca_slli_low_row_hwir("strict_slli", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_slli_low_row_hwir("strict_slli", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.slli.low")
    expect(module.summary.comb_op_count).to_equal(15)
    expect(module.select_ops[0].condition).to_equal("is_c_slli_low")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct the five-bit C.SRLI row only for a critical product

- should construct the five-bit C.SRLI row only for a critical product
- Build the five-bit C.SRLI semantic row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.srli.low`
   - Expected: module.summary.comb_op_count equals `16`
   - Expected: module.select_ops[0].condition equals `is_c_srli_low`
   - Expected: module.constants[1].value equals `64515`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct the five-bit C.SRLI row only for a critical product")
step("Build the five-bit C.SRLI semantic row under rejected and admitted critical profiles")
val rejected = strict_zca_srli_low_row_hwir("strict_srli", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_srli_low_row_hwir("strict_srli", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.srli.low")
    expect(module.summary.comb_op_count).to_equal(16)
    expect(module.select_ops[0].condition).to_equal("is_c_srli_low")
    expect(module.constants[1].value).to_equal(64515)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct the five-bit C.SRAI row only for a critical product

- should construct the five-bit C.SRAI row only for a critical product
- Build the five-bit C.SRAI semantic row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.srai.low`
   - Expected: module.summary.comb_op_count equals `17`
   - Expected: module.select_ops[0].condition equals `is_c_srai_low`
   - Expected: module.constants[1].value equals `64515`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct the five-bit C.SRAI row only for a critical product")
step("Build the five-bit C.SRAI semantic row under rejected and admitted critical profiles")
val rejected = strict_zca_srai_low_row_hwir("strict_srai", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_srai_low_row_hwir("strict_srai", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.srai.low")
    expect(module.summary.comb_op_count).to_equal(17)
    expect(module.select_ops[0].condition).to_equal("is_c_srai_low")
    expect(module.constants[1].value).to_equal(64515)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct signed-immediate C.ANDI only for a critical product

- should construct signed-immediate C.ANDI only for a critical product
- Build the signed-immediate C.ANDI row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.andi`
   - Expected: module.summary.comb_op_count equals `22`
   - Expected: module.select_ops[1].condition equals `is_c_andi`
   - Expected: module.constants[1].value equals `60419`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct signed-immediate C.ANDI only for a critical product")
step("Build the signed-immediate C.ANDI row under rejected and admitted critical profiles")
val rejected = strict_zca_candi_row_hwir("strict_candi", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_candi_row_hwir("strict_candi", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.andi")
    expect(module.summary.comb_op_count).to_equal(22)
    expect(module.select_ops[1].condition).to_equal("is_c_andi")
    expect(module.constants[1].value).to_equal(60419)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct compact-register C.SUB only for a critical product

- should construct compact-register C.SUB only for a critical product
- Build the compact-register C.SUB row under rejected and admitted critical profiles
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.sub`
   - Expected: module.summary.comb_op_count equals `18`
   - Expected: module.select_ops[0].condition equals `is_c_sub`
   - Expected: module.constants[1].value equals `64611`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct compact-register C.SUB only for a critical product")
step("Build the compact-register C.SUB row under rejected and admitted critical profiles")
val rejected = strict_zca_csub_row_hwir("strict_csub", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_csub_row_hwir("strict_csub", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.sub")
    expect(module.summary.comb_op_count).to_equal(18)
    expect(module.select_ops[0].condition).to_equal("is_c_sub")
    expect(module.constants[1].value).to_equal(64611)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct compact-register C.XOR through the same critical elaborator

- should construct compact-register C.XOR through the same critical elaborator
- Build the compact-register C.XOR row through the selected critical elaborator
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.xor`
   - Expected: module.summary.comb_op_count equals `18`
   - Expected: module.select_ops[0].condition equals `is_c_xor`
   - Expected: module.constants[1].value equals `64611`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct compact-register C.XOR through the same critical elaborator")
step("Build the compact-register C.XOR row through the selected critical elaborator")
val rejected = strict_zca_cxor_row_hwir("strict_cxor", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_cxor_row_hwir("strict_cxor", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.xor")
    expect(module.summary.comb_op_count).to_equal(18)
    expect(module.select_ops[0].condition).to_equal("is_c_xor")
    expect(module.constants[1].value).to_equal(64611)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct compact-register C.OR through the same critical elaborator

- should construct compact-register C.OR through the same critical elaborator
- Build the compact-register C.OR row through the selected critical elaborator
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.or`
   - Expected: module.summary.comb_op_count equals `18`
   - Expected: module.select_ops[0].condition equals `is_c_or`
   - Expected: module.constants[1].value equals `64611`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct compact-register C.OR through the same critical elaborator")
step("Build the compact-register C.OR row through the selected critical elaborator")
val rejected = strict_zca_cor_row_hwir("strict_cor", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_cor_row_hwir("strict_cor", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.or")
    expect(module.summary.comb_op_count).to_equal(18)
    expect(module.select_ops[0].condition).to_equal("is_c_or")
    expect(module.constants[1].value).to_equal(64611)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct compact-register C.AND through the same critical elaborator

- should construct compact-register C.AND through the same critical elaborator
- Build the compact-register C.AND row through the selected critical elaborator
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.and`
   - Expected: module.summary.comb_op_count equals `18`
   - Expected: module.select_ops[0].condition equals `is_c_and`
   - Expected: module.constants[1].value equals `64611`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct compact-register C.AND through the same critical elaborator")
step("Build the compact-register C.AND row through the selected critical elaborator")
val rejected = strict_zca_cand_row_hwir("strict_cand", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_cand_row_hwir("strict_cand", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.and")
    expect(module.summary.comb_op_count).to_equal(18)
    expect(module.select_ops[0].condition).to_equal("is_c_and")
    expect(module.constants[1].value).to_equal(64611)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct C.JR with a reserved-register rejection path

- should construct C.JR with a reserved-register rejection path
- Build C.JR and exercise its reserved-register rejection boundary
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.jr`
   - Expected: module.summary.comb_op_count equals `10`
   - Expected: module.select_ops[1].condition equals `rd_is_zero`
   - Expected: module.constants[1].value equals `61567`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct C.JR with a reserved-register rejection path")
step("Build C.JR and exercise its reserved-register rejection boundary")
val rejected = strict_zca_cjr_row_hwir("strict_cjr", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_cjr_row_hwir("strict_cjr", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.jr")
    expect(module.summary.comb_op_count).to_equal(10)
    expect(module.select_ops[1].condition).to_equal("rd_is_zero")
    expect(module.constants[1].value).to_equal(61567)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct C.MV with hint normalization and C.JR exclusion

- should construct C.MV with hint normalization and C.JR exclusion
- Build C.MV and inspect its normalized hint and C.JR exclusion path
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.mv`
   - Expected: module.summary.comb_op_count equals `16`
   - Expected: module.select_ops[1].condition equals `rd_is_zero`
   - Expected: module.select_ops[2].condition equals `rs2_is_zero`
   - Expected: module.constants[1].value equals `61443`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct C.MV with hint normalization and C.JR exclusion")
step("Build C.MV and inspect its normalized hint and C.JR exclusion path")
val rejected = strict_zca_cmv_row_hwir("strict_cmv", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_cmv_row_hwir("strict_cmv", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.mv")
    expect(module.summary.comb_op_count).to_equal(16)
    expect(module.select_ops[1].condition).to_equal("rd_is_zero")
    expect(module.select_ops[2].condition).to_equal("rs2_is_zero")
    expect(module.constants[1].value).to_equal(61443)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should construct C.JALR with a reserved-register rejection path

- should construct C.JALR with a reserved-register rejection path
- Build C.JALR and exercise its reserved-register rejection boundary
   - Expected: rejected.is_err() is true
   - Expected: module.shape_diagnostic() equals ``
   - Expected: module.origins[0].source_name equals `zca.c.jalr`
   - Expected: module.summary.comb_op_count equals `11`
   - Expected: module.select_ops[1].condition equals `rd_is_zero`
   - Expected: module.constants[1].value equals `61567`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should construct C.JALR with a reserved-register rejection path")
step("Build C.JALR and exercise its reserved-register rejection boundary")
val rejected = strict_zca_cjalr_row_hwir("strict_cjalr", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val built = strict_zca_cjalr_row_hwir("strict_cjalr", CoreConfig.rv64_zca_mission_critical())
if val module = built.ok():
    expect(module.shape_diagnostic()).to_equal("")
    expect(module.origins[0].source_name).to_equal("zca.c.jalr")
    expect(module.summary.comb_op_count).to_equal(11)
    expect(module.select_ops[1].condition).to_equal("rd_is_zero")
    expect(module.constants[1].value).to_equal(61567)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should specialize C.ADD x0 hint behavior before RTL emission

- should specialize C.ADD x0 hint behavior before RTL emission
- Build C.ADD with the x0 hint behavior before strict rendering
   - Expected: rejected.is_err() is true
   - Expected: module32.shape_diagnostic() equals ``
   - Expected: module32.origins[0].source_name equals `zca.c.add`
   - Expected: module32.summary.comb_op_count equals `18`
   - Expected: module32.select_ops[1].condition equals `rd_is_zero`
   - Expected: render_strict_hwir_vhdl(module32).is_success() is true
   - Expected: false is true
   - Expected: module64.shape_diagnostic() equals ``
   - Expected: module64.summary.comb_op_count equals `16`
   - Expected: module64.signals.len() equals `15`
   - Expected: render_strict_hwir_vhdl(module64).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should specialize C.ADD x0 hint behavior before RTL emission")
step("Build C.ADD with the x0 hint behavior before strict rendering")
val rejected = strict_zca_cadd_row_hwir("strict_cadd", CoreConfig.rv32())
expect(rejected.is_err()).to_equal(true)
val rv32 = strict_zca_cadd_row_hwir("strict_cadd32", CoreConfig.rv32_zca_mission_critical())
val rv64 = strict_zca_cadd_row_hwir("strict_cadd64", CoreConfig.rv64_zca_mission_critical())
if val module32 = rv32.ok():
    expect(module32.shape_diagnostic()).to_equal("")
    expect(module32.origins[0].source_name).to_equal("zca.c.add")
    expect(module32.summary.comb_op_count).to_equal(18)
    expect(module32.select_ops[1].condition).to_equal("rd_is_zero")
    expect(render_strict_hwir_vhdl(module32).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
if val module64 = rv64.ok():
    expect(module64.shape_diagnostic()).to_equal("")
    expect(module64.summary.comb_op_count).to_equal(16)
    expect(module64.signals.len()).to_equal(15)
    expect(render_strict_hwir_vhdl(module64).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject output operands and duplicate origin identities at the critical boundary

- should reject output operands and duplicate origin identities at the critical boundary
- Construct critical typed graphs with invalid output operands and duplicate origins
   - Expected: module.shape_diagnostic() equals `HWIR-E-OP-OPERAND-DIRECTION: operation operands must be input ports`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject output operands and duplicate origin identities at the critical boundary")
step("Construct critical typed graphs with invalid output operands and duplicate origins")
val lower = strict_rv32_result()
if val module = lower.module:
    module.comb_ops = [HwCombOp.binary("and", "out_c", "out_c", "in_b", 32)]
    expect(module.shape_diagnostic()).to_equal("HWIR-E-OP-OPERAND-DIRECTION: operation operands must be input ports")
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a second combinational driver for one result at the critical boundary

- should reject a second combinational driver for one result at the critical boundary
- Add a second combinational driver to one typed result
   - Expected: module.shape_diagnostic() equals `HWIR-E-MULTIPLE-DRIVER: each strict combinational result must have one driver`
   - Expected: module.shape_diagnostic() equals `HWIR-E-DUPLICATE-ORIGIN: origin IDs must be distinct from the module and each... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a second combinational driver for one result at the critical boundary")
step("Add a second combinational driver to one typed result")
val summary = HwModule(name: "duplicate_driver", profile: "rv32", port_count: 3,
    signal_count: 1, register_count: 0, memory_count: 0, comb_op_count: 2,
    clock_domain_count: 1, fallback_function: "", cost: HwCostModel.empty())
val module = HwModuleDef(summary: summary, config: CoreConfig.rv32(),
    node_id: HwNodeId.module_root("duplicate_driver"),
    origins: [HwOrigin(node_id: HwNodeId.child("duplicate_driver", "root"), source_name: "duplicate_driver")],
    ports: [HwPort.input("a", "Bits", 32), HwPort.input("b", "Bits", 32), HwPort.output("out_c", "Bits", 32)],
    signals: [HwSignal(name: "shared_val", type_name: "Bits", bit_width: 32, driver_count: 2, source_id: "")],
    constants: [],
    comb_ops: [
        HwCombOp.binary("and", "shared_val", "a", "b", 32),
        HwCombOp.binary("or", "shared_val", "a", "b", 32)
    ],
    compare_ops: [], select_ops: [],
    clock_domains: [HwClockDomain.default_domain()])
expect(module.shape_diagnostic()).to_equal("HWIR-E-MULTIPLE-DRIVER: each strict combinational result must have one driver")
val fresh = strict_rv32_result()
if val module = fresh.module:
    module.origins = [HwOrigin(node_id: module.node_id, source_name: "duplicate")]
    expect(module.shape_diagnostic()).to_equal("HWIR-E-DUPLICATE-ORIGIN: origin IDs must be distinct from the module and each other")
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a non-bit predicate before select emission at the critical boundary

- should reject a non-bit predicate before select emission at the critical boundary
- Use a non-bit predicate in a typed select before strict emission
   - Expected: module.shape_diagnostic() equals `HWIR-E-SELECT-CONDITION: select condition must be a readable one-bit value`
   - Expected: render_strict_hwir_vhdl(module).is_success() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a non-bit predicate before select emission at the critical boundary")
step("Use a non-bit predicate in a typed select before strict emission")
val summary = HwModule(name: "bad_select", profile: "riscv-gen2-rv32-zca-critical", port_count: 1,
    signal_count: 0, register_count: 0, memory_count: 0, comb_op_count: 1,
    clock_domain_count: 1, fallback_function: "", cost: HwCostModel.empty())
val module = HwModuleDef(summary: summary, config: CoreConfig.rv32_zca_mission_critical(),
    node_id: HwNodeId.module_root("bad_select"),
    origins: [HwOrigin(node_id: HwNodeId.child("bad_select", "select"), source_name: "bad_select")],
    ports: [HwPort.output("canonical_instruction", "Bits", 32)], signals: [],
    constants: [
        HwConstant.bits("wide_condition", 32, 1),
        HwConstant.bits("when_true", 32, 1048691),
        HwConstant.bits("when_false", 32, 0)
    ],
    comb_ops: [], compare_ops: [],
    select_ops: [HwSelectOp.mux("canonical_instruction", "wide_condition", "when_true", "when_false", 32)],
    clock_domains: [HwClockDomain.default_domain()])
expect(module.shape_diagnostic()).to_equal("HWIR-E-SELECT-CONDITION: select condition must be a readable one-bit value")
expect(render_strict_hwir_vhdl(module).is_success()).to_equal(false)
```

</details>

#### should reject names that would need VHDL sanitization at the critical boundary

- should reject names that would need VHDL sanitization at the critical boundary
- Assign a non-serializable identifier before strict VHDL rendering
   - Expected: emitted.is_success() is false
   - Expected: emitted.diagnostic equals `HWIR-E-VHDL-IDENTIFIER: module name is not a stable VHDL identifier`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject names that would need VHDL sanitization at the critical boundary")
step("Assign a non-serializable identifier before strict VHDL rendering")
val lower = strict_rv32_result()
if val module = lower.module:
    module.summary.name = "not a vhdl entity"
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(false)
    expect(emitted.diagnostic).to_equal("HWIR-E-VHDL-IDENTIFIER: module name is not a stable VHDL identifier")
else:
    expect(false).to_equal(true)
```

</details>

#### should emit stateful products only from typed sequential HWIR plans

- should emit stateful products only from typed sequential HWIR plans
- Compile the typed parcel and trap stateful frontend products
   - Expected: parcel.is_success() is true
   - Expected: trap.is_success() is true
   - Expected: parcel.route equals `hwir-gen2-stateful-product-v2`
   - Expected: trap.route equals `hwir-gen2-trap-stateful-product-v3`
   - Expected: parcel.hwir_graph_sha256.len() equals `64`
   - Expected: trap.hwir_graph_sha256.len() equals `64`
   - Expected: parcel.uses_legacy_fallback() is false
   - Expected: trap.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should emit stateful products only from typed sequential HWIR plans")
step("Compile the typed parcel and trap stateful frontend products")
val parcel = compile_strict_zca_single_outstanding_frontend_product(CoreConfig.rv32_zca_mission_critical())
val trap = compile_strict_zca_trap_single_outstanding_frontend_product(CoreConfig.rv64_zca_mission_critical())
expect(parcel.is_success()).to_equal(true)
expect(trap.is_success()).to_equal(true)
expect(parcel.route).to_equal("hwir-gen2-stateful-product-v2")
expect(trap.route).to_equal("hwir-gen2-trap-stateful-product-v3")
expect(parcel.hwir_graph_sha256.len()).to_equal(64)
expect(trap.hwir_graph_sha256.len()).to_equal(64)
expect(parcel.vhdl).to_contain("elsif retire_valid='1' and valid_reg='1' and issued_reg='1' and retire_lineage=lineage_reg and retire_original_parcel=parcel_reg and retire_canonical_instruction=decoder_canonical and retire_original_length_bytes=decoder_length and lineage_reg=(others=>'1') then valid_reg <= '0'; issued_reg <= '0'; fault_reg <= retire_valid;")
expect(parcel.vhdl).to_contain("elsif retire_valid='1' and valid_reg='1' and issued_reg='1' and retire_lineage=lineage_reg and retire_original_parcel=parcel_reg and retire_canonical_instruction=decoder_canonical and retire_original_length_bytes=decoder_length then")
expect(parcel.vhdl).to_contain("fetch_ready <= '1' when valid_reg='0' and fault_reg='0' else '0';")
expect(trap.vhdl).to_contain("trap_valid <= '1' when decoder_trap_valid='1' and valid_reg='1' and issued_reg='0' and fault_reg='0' else '0';")
expect(trap.vhdl).to_contain("canonical_instruction <= decoder_canonical when valid_reg='1' and issued_reg='0' and fault_reg='0' else (others=>'0')")
expect(parcel.uses_legacy_fallback()).to_equal(false)
expect(trap.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should quarantine retirement composition emission until a typed producer receipt exists

- should quarantine retirement composition emission until a typed producer receipt exists
- Render a retirement composition with a rejected producer-emission receipt
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-RETIRE-COMPOSITION-UNSUPPORTED: closed retirement composition requires... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should quarantine retirement composition emission until a typed producer receipt exists")
step("Render a retirement composition with a rejected producer-emission receipt")
val built = strict_zca_single_outstanding_retirement_composition(
    "riscv_gen2_closed_retirement_rv32", CoreConfig.rv32_zca_mission_critical(),
    "riscv_gen2_retire_receipt_child_rv32")
if val composition = built.ok():
    val frontend = compile_strict_zca_single_outstanding_frontend_product(composition.config)
    val forged = HwirStrictVhdlResult.rejected("unproven producer")
    val result = render_strict_retirement_composition_vhdl(composition, frontend, forged)
    expect(result.is_success()).to_equal(false)
    expect(result.diagnostic).to_equal("HWIR-E-RETIRE-COMPOSITION-UNSUPPORTED: closed retirement composition requires a typed architectural producer emission receipt")
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a sequential plan whose assignment width no longer matches state

- should reject a sequential plan whose assignment width no longer matches state
- Change a sequential assignment width after building the typed frontend
   - Expected: frontend.shape_diagnostic() equals `HWIR-E-SEQUENTIAL-ASSIGNMENT: sequential assignment value width must match it... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a sequential plan whose assignment width no longer matches state")
step("Change a sequential assignment width after building the typed frontend")
val built = strict_zca_single_outstanding_frontend_hwir("bad_state_plan", CoreConfig.rv32_zca_mission_critical())
if val frontend = built.ok():
    val rule0 = frontend.sequential.rules[0]
    val rule0_assign = rule0.assignments[0]
    rule0_assign.value.bit_width = 2
    rule0.assignments[0] = rule0_assign
    frontend.sequential.rules[0] = rule0
    expect(frontend.shape_diagnostic()).to_equal("HWIR-E-SEQUENTIAL-ASSIGNMENT: sequential assignment value width must match its register")
else:
    expect(false).to_equal(true)
```

</details>

#### should reject unsafe sequential identifiers before VHDL serialization

- should reject unsafe sequential identifiers before VHDL serialization
- Assign an unsafe register identifier before sequential VHDL serialization
   - Expected: frontend.shape_diagnostic() equals `HWIR-E-SEQUENTIAL-REGISTER: sequential registers must be unique and valid`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject unsafe sequential identifiers before VHDL serialization")
step("Assign an unsafe register identifier before sequential VHDL serialization")
val built = strict_zca_single_outstanding_frontend_hwir("bad_identifier_plan", CoreConfig.rv32_zca_mission_critical())
if val frontend = built.ok():
    val reg0 = frontend.sequential.registers[0]
    reg0.name = "bad state"
    frontend.sequential.registers[0] = reg0
    expect(frontend.shape_diagnostic()).to_equal("HWIR-E-SEQUENTIAL-REGISTER: sequential registers must be unique and valid")
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_foundation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V Gen2 strict HWIR foundation.
- RISC-V Gen2 strict HWIR foundation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 50 |
| Active scenarios | 50 |
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

- Canonical SPipe generation for source `77b9944fe59c50cc52e9bfe9dca66ee47bd495bdf8be21a52b6a01943e541e9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `77b9944fe59c50cc52e9bfe9dca66ee47bd495bdf8be21a52b6a01943e541e9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `77b9944fe59c50cc52e9bfe9dca66ee47bd495bdf8be21a52b6a01943e541e9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/compiler/50.mir/hwir_foundation_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_foundation_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_foundation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_foundation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 43 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should construct stable typed origins and concrete ports' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should construct stable typed origins and concrete ports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind strict artifact provenance to the canonical typed graph' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind strict artifact provenance to the canonical typed graph' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use length-prefixed graph fields to prevent delimiter hash ambiguity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use length-prefixed graph fields to prevent delimiter hash ambiguity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind delimiter-bearing origin lineage without graph-hash aliasing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should specialize RV32 and RV64 at elaboration time' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_foundation_spec.spl:127:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject invalid elaboration configuration' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
