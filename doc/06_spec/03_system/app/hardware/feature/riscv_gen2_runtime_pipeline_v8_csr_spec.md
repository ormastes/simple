# RISC-V Gen2 V8 flattened Zmmul plus Zicsr runtime pipeline

Status: development structural evidence. The current self-hosted-runtime and
clocked-GHDL qualification lanes are blocked until their admitted runners
execute the matching V8 scenarios; neither a bootstrap-runner result nor these
source/topology assertions is a qualification PASS.

> Exercises the public V8 product boundary for the combined base-I, Zmmul, Zicsr,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V Gen2 V8 flattened Zmmul plus Zicsr runtime pipeline

Exercises the public V8 product boundary for the combined base-I, Zmmul, Zicsr,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v8_csr_spec.spl` |
| Updated | 2026-08-13 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the public V8 product boundary for the combined base-I, Zmmul, Zicsr,
and Zifencei profiles.  It proves construction, direct tag-three routing, the
CSR service ABI, and deterministic strict lowering.  The separate clocked GHDL
scenario is the behavioral evidence lane; this structural scenario does not
claim that GHDL or a self-hosted runtime has qualified the product.

## Scenarios

### RISC-V Gen2 V8 flattened Zmmul plus Zicsr runtime pipeline

#### should elaborate RV32 and RV64 combined Zmmul and Zicsr products with one tag-three CSR owner

- Build concrete RV32 and RV64 V8 combined runtime pipelines
- Check the closed product topology and its dynamic CSR owner
   - Expected: rv32.diagnostic() equals ``
   - Expected: rv64.diagnostic() equals ``
   - Expected: rv32.csr.entity_name equals `runtime_v8_system_rv32_csr`
   - Expected: rv64.csr.entity_name equals `runtime_v8_system_rv64_csr`
   - Expected: rv32.muldiv.entity_name equals `runtime_v8_system_rv32_muldiv`
   - Expected: rv64.muldiv.entity_name equals `runtime_v8_system_rv64_muldiv`
   - Expected: rv32.router.entity_name equals `runtime_v8_system_rv32_router`
   - Expected: rv64.router.entity_name equals `runtime_v8_system_rv64_router`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build concrete RV32 and RV64 V8 combined runtime pipelines")
val rv32 = strict_riscv_scalar_runtime_pipeline_v8_flat_direct(
    "runtime_v8_system_rv32", runtime_v8_zmmul_zicsr_config(32),
    LsuConfig.rv32_product_default()).unwrap()
val rv64 = strict_riscv_scalar_runtime_pipeline_v8_flat_direct(
    "runtime_v8_system_rv64", runtime_v8_zmmul_zicsr_config(64),
    LsuConfig.rv64_product_default()).unwrap()
step("Check the closed product topology and its dynamic CSR owner")
expect(rv32.diagnostic()).to_equal("")
expect(rv64.diagnostic()).to_equal("")
expect(rv32.csr.entity_name).to_equal("runtime_v8_system_rv32_csr")
expect(rv64.csr.entity_name).to_equal("runtime_v8_system_rv64_csr")
expect(rv32.muldiv.entity_name).to_equal("runtime_v8_system_rv32_muldiv")
expect(rv64.muldiv.entity_name).to_equal("runtime_v8_system_rv64_muldiv")
expect(rv32.router.entity_name).to_equal("runtime_v8_system_rv32_router")
expect(rv64.router.entity_name).to_equal("runtime_v8_system_rv64_router")
```

</details>

#### should expose the XLEN-aware CSR lookup and exact-once commit service boundary

- Build both supported combined profile variants
- Check the frozen external CSR service ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build both supported combined profile variants")
for row in [(runtime_v8_zmmul_zicsr_config(32), LsuConfig.rv32_product_default()),
        (runtime_v8_zmmul_zicsr_config(64), LsuConfig.rv64_product_default())]:
    val pipeline = strict_riscv_scalar_runtime_pipeline_v8_flat_direct(
        "runtime_v8_system_csr_" + row[0].xlen.to_text(), row[0], row[1]).unwrap()
    step("Check the frozen external CSR service ports")
    for port in [("csr_present", "in", 1), ("csr_read_value", "in", row[0].xlen),
            ("csr_lookup_valid", "out", 1), ("csr_lookup_address", "out", 12),
            ("csr_lookup_read_enable", "out", 1), ("csr_commit_valid", "out", 1),
            ("csr_commit_address", "out", 12), ("csr_commit_value", "out", row[0].xlen)]:
        expect(pipeline.top_ports.any(_.name == port[0] and _.direction == port[1] and
            _.bit_width == port[2])).to_equal(true)
```

</details>

#### should bind accepted CSR work completion readiness and fail-closed fault through tag three

- Build an RV64 combined product for protocol-edge inspection
- Trace pending-owner tag-three request completion commit and fault paths
   - Expected: pipeline.router.constants.any(_.name == "class6" and _.value == 6) is true
   - Expected: pipeline.router.constants.any(_.name == "tag_csr" and _.value == 3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build an RV64 combined product for protocol-edge inspection")
val pipeline = strict_riscv_scalar_runtime_pipeline_v8_flat_direct(
    "runtime_v8_system_edges", runtime_v8_zmmul_zicsr_config(64),
    LsuConfig.rv64_product_default()).unwrap()
step("Trace pending-owner tag-three request completion commit and fault paths")
for edge in [("pending", "csr_request_valid", "csr", "request_valid", 1),
        ("pending", "csr_request_provider_tag", "csr", "request_provider_tag", 3),
        ("csr", "request_accept", "pending", "csr_request_accept", 1),
        ("csr", "completion_valid", "pending", "csr_completion_valid", 1),
        ("pending", "csr_completion_ready", "csr", "completion_ready", 1),
        ("csr", "provider_protocol_fault", "global_fault_gate", "csr_fault", 1),
        ("csr", "csr_commit_valid", "global_fault_gate", "raw_csr_commit_valid", 1)]:
    expect(pipeline.bindings.any(_.source_owner == edge[0] and _.source_port == edge[1] and
        _.destination_owner == edge[2] and _.destination_port == edge[3] and
        _.bit_width == edge[4])).to_equal(true)
expect(pipeline.router.constants.any(_.name == "class6" and _.value == 6)).to_equal(true)
expect(pipeline.router.constants.any(_.name == "tag_csr" and _.value == 3)).to_equal(true)
```

</details>

#### should emit a deterministic strict VHDL V8-flat combined product

- Compile the same RV32 combined product twice through the public route
- Check route identity graph determinism and both dynamic-provider instances
   - Expected: first.is_success() is true
   - Expected: second.is_success() is true
   - Expected: first.route equals `hwir-gen2-scalar-runtime-pipeline-v8-flat-direct`
   - Expected: first.hwir_graph_sha256 equals `second.hwir_graph_sha256`
   - Expected: first.vhdl equals `second.vhdl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compile the same RV32 combined product twice through the public route")
val first = compile_strict_riscv_scalar_runtime_pipeline_v8_flat(
    "runtime_v8_system_vhdl", runtime_v8_zmmul_zicsr_config(32),
    LsuConfig.rv32_product_default())
val second = compile_strict_riscv_scalar_runtime_pipeline_v8_flat(
    "runtime_v8_system_vhdl", runtime_v8_zmmul_zicsr_config(32),
    LsuConfig.rv32_product_default())
step("Check route identity graph determinism and both dynamic-provider instances")
expect(first.is_success()).to_equal(true)
expect(second.is_success()).to_equal(true)
expect(first.route).to_equal("hwir-gen2-scalar-runtime-pipeline-v8-flat-direct")
expect(first.hwir_graph_sha256).to_equal(second.hwir_graph_sha256)
expect(first.vhdl).to_equal(second.vhdl)
expect(first.vhdl).to_contain("simple-hwir v8-flat-route-receipt=")
expect(first.vhdl).to_contain("muldiv: entity work.runtime_v8_system_vhdl_muldiv")
expect(first.vhdl).to_contain("csr: entity work.runtime_v8_system_vhdl_csr")
expect(first.vhdl).to_contain("csr_commit_value : out std_logic_vector(31 downto 0)")
```

</details>

#### should reject IM and standalone Zicsr profiles outside the combined product boundary

- Attempt construction with profiles that would falsely claim a full M or Zicsr-only product


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attempt construction with profiles that would falsely claim a full M or Zicsr-only product")
expect(strict_riscv_scalar_runtime_pipeline_v8_flat_direct(
    "runtime_v8_system_im_rejected", CoreConfig.rv32im(),
    LsuConfig.rv32_product_default()).is_err()).to_equal(true)
expect(strict_riscv_scalar_runtime_pipeline_v8_flat_direct(
    "runtime_v8_system_zicsr_rejected", CoreConfig.rv32_zicsr_zifencei(),
    LsuConfig.rv32_product_default()).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
