# RV32 External Formal Harness Spec

> 1. cleanup bundle dir

<!-- sdn-diagram:id=rv32_external_formal_harness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_external_formal_harness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_external_formal_harness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_external_formal_harness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32 External Formal Harness Spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/rv32_external_formal_harness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### RV32 external formal harness

#### generates the harness bundle files

1. cleanup bundle dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fresh_bundle()
expect(result.is_ok()).to_equal(true)
val bundle = result.unwrap()
expect(rt_file_exists(bundle.harness_path)).to_equal(true)
expect(rt_file_exists(bundle.sby_path)).to_equal(true)
expect(rt_file_exists(bundle.manifest_path)).to_equal(true)
cleanup_bundle_dir(bundle.root_dir)
```

</details>

#### writes a harness with rv32i_core assertions

1. cleanup bundle dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bundle = fresh_bundle().unwrap()
val text = read_generated_bundle_file(bundle.harness_path)
expect(text).to_contain("entity rv32i_core_external_formal")
expect(text).to_contain("entity work.rv32i_core")
expect(text).to_contain("instruction fetch address must stay halfword aligned")
expect(text).to_contain("halfword memory accesses must stay halfword aligned")
expect(text).to_contain("halted must be sticky once asserted")
expect(text).to_contain("unexpected semihost operation observed")
expect(text).to_contain("rvfi_valid")
expect(text).to_contain("rvfi_insn must mirror fetched instruction")
expect(text).to_contain("rvfi_pc_rdata must mirror instruction address")
cleanup_bundle_dir(bundle.root_dir)
```

</details>

#### writes an sby file tied to the rv32 rtl set

1. cleanup bundle dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bundle = fresh_bundle().unwrap()
val text = read_generated_bundle_file(bundle.sby_path)
expect(text).to_contain("mode prove")
expect(text).to_contain("rv32i_core_external_formal")
expect(text).to_contain("examples/09_embedded/fpga_riscv/rtl/rv32i_core.vhd")
expect(text).to_contain("rv32i_core_external_formal.vhd")
cleanup_bundle_dir(bundle.root_dir)
```

</details>

#### writes a manifest describing the proof bundle

1. cleanup bundle dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bundle = fresh_bundle().unwrap()
val text = read_generated_bundle_file(bundle.manifest_path)
expect(text).to_contain("arch = \"riscv32\"")
expect(text).to_contain("proof_style = \"rvfi_structural\"")
expect(text).to_contain("runner = \"sby -f rv32i_core_external.sby\"")
cleanup_bundle_dir(bundle.root_dir)
```

</details>

#### matches the lane registry contract for riscv_external_formal

1. Some
   - Expected: l.target_arch equals `riscv32`
   - Expected: l.adapter_kind equals `AdapterKind.external_formal`
   - Expected: l.primary_result_channel equals `ResultChannelKind.exit_code`
   - Expected: l.status equals `LaneStatus.transport_only`
   - Expected: l.authoritative_spec_path equals `test/system/hardware/rv32_external_formal_harness_spec.spl`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("riscv_external_formal")
match lane:
    Some(l):
        expect(l.target_arch).to_equal("riscv32")
        expect(l.adapter_kind).to_equal(AdapterKind.external_formal)
        expect(l.primary_result_channel).to_equal(ResultChannelKind.exit_code)
        expect(l.status).to_equal(LaneStatus.transport_only)
        expect(l.authoritative_spec_path).to_equal("test/system/hardware/rv32_external_formal_harness_spec.spl")
    nil:
        expect(false).to_equal(true)
```

</details>

#### probes riscv_external_formal through the lane registry

1. Some
   - Expected: dispatched.lane_id equals `riscv_external_formal`
   - Expected: dispatched.status equals `direct.status`
   - Expected: dispatched.tool_name equals `direct.tool_name`
   - Expected: dispatched.detail equals `direct.detail`
   - Expected: dispatched.is_acceptable() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("riscv_external_formal")
match lane:
    Some(l):
        val direct = probe_external_formal()
        val dispatched = probe_for_lane(l)
        expect(dispatched.lane_id).to_equal("riscv_external_formal")
        expect(dispatched.status).to_equal(direct.status)
        expect(dispatched.tool_name).to_equal(direct.tool_name)
        expect(dispatched.detail).to_equal(direct.detail)
        expect(dispatched.is_acceptable()).to_equal(true)
    nil:
        expect(false).to_equal(true)
```

</details>

#### keeps runtime and registry probe semantics aligned

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = probe_riscv_external_formal()
val registry = probe_external_formal()
expect(runtime.is_runnable()).to_equal(registry.is_runnable())
expect(runtime.detail).to_equal(registry.detail)
```

</details>

#### documents skip behavior when the external formal lane is not runnable

1. Some
   - Expected: report.status.to_text() equals `skip_missing_tool`
   - Expected: report.is_acceptable() is true
   - Expected: packet.is_skip() is true
   - Expected: packet.channel equals `exit_code`
   - Expected: verifier.verify(packet).is_ok() is true
2. cleanup bundle dir
   - Expected: report.is_runnable() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("riscv_external_formal")
match lane:
    Some(l):
        val report = probe_for_lane(l)
        if not report.is_runnable():
            val bundle = fresh_bundle().unwrap()
            val packet = run_rv32_external_formal_packet(bundle)
            expect(report.status.to_text()).to_equal("skip_missing_tool")
            expect(report.is_acceptable()).to_equal(true)
            expect(packet.is_skip()).to_equal(true)
            expect(packet.channel).to_equal("exit_code")
            val verifier = ResultVerifier.allow_skip()
            expect(verifier.verify(packet).is_ok()).to_equal(true)
            cleanup_bundle_dir(bundle.root_dir)
        else:
            expect(report.is_runnable()).to_equal(true)
    nil:
        expect(false).to_equal(true)
```

</details>

#### verifies the lane result via the canonical exit-code packet path

1. Some
2. cleanup bundle dir
   - Expected: packet.lane_id equals `l.lane_id`
   - Expected: packet.channel equals `exit_code`
   - Expected: verifier.verify(packet).is_ok() is true
3. cleanup bundle dir
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("riscv_external_formal")
match lane:
    Some(l):
        val bundle = fresh_bundle().unwrap()
        val packet = run_rv32_external_formal_packet(bundle)
        if packet.is_skip():
            cleanup_bundle_dir(bundle.root_dir)
            return "skip: {packet.output}"
        expect(packet.lane_id).to_equal(l.lane_id)
        expect(packet.channel).to_equal("exit_code")
        val verifier = ResultVerifier.default_pass()
        expect(verifier.verify(packet).is_ok()).to_equal(true)
        cleanup_bundle_dir(bundle.root_dir)
    nil:
        expect(false).to_equal(true)
```

</details>

#### runs the external formal bundle when tools are available

1. cleanup bundle dir
   - Expected: result.is_ok() is true
2. cleanup bundle dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = probe_external_formal()
val bundle = fresh_bundle().unwrap()
if not report.is_runnable():
    cleanup_bundle_dir(bundle.root_dir)
    return "skip: {report.detail}"
else:
    val result = run_rv32_external_formal(bundle)
    expect(result.is_ok()).to_equal(true)
    cleanup_bundle_dir(bundle.root_dir)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
