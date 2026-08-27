# RV32 External Formal Harness Spec

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### RV32 external formal harness

#### generates the harness bundle files

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates the harness bundle files
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(bundle.harness_path) is true
   - Expected: rt_file_exists(bundle.sby_path) is true
   - Expected: rt_file_exists(bundle.manifest_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates the harness bundle files")
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

- writes a harness with rv32i_core assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes a harness with rv32i_core assertions")
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

- writes an sby file tied to the rv32 rtl set


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes an sby file tied to the rv32 rtl set")
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

- writes a manifest describing the proof bundle


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes a manifest describing the proof bundle")
val bundle = fresh_bundle().unwrap()
val text = read_generated_bundle_file(bundle.manifest_path)
expect(text).to_contain("arch = \"riscv32\"")
expect(text).to_contain("proof_style = \"rvfi_structural\"")
expect(text).to_contain("runner = \"sby -f rv32i_core_external.sby\"")
cleanup_bundle_dir(bundle.root_dir)
```

</details>

#### matches the lane registry contract for riscv_external_formal

- matches the lane registry contract for riscv_external_formal
   - Expected: l.target_arch equals `riscv32`
   - Expected: l.adapter_kind equals `AdapterKind.external_formal`
   - Expected: l.primary_result_channel equals `ResultChannelKind.exit_code`
   - Expected: l.status equals `LaneStatus.transport_only`
   - Expected: l.authoritative_spec_path equals `test/system/hardware/rv32_external_formal_harness_spec.spl`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches the lane registry contract for riscv_external_formal")
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

- probes riscv_external_formal through the lane registry
   - Expected: dispatched.lane_id equals `riscv_external_formal`
   - Expected: dispatched.status equals `direct.status`
   - Expected: dispatched.tool_name equals `direct.tool_name`
   - Expected: dispatched.detail equals `direct.detail`
   - Expected: dispatched.is_acceptable() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("probes riscv_external_formal through the lane registry")
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

- keeps runtime and registry probe semantics aligned
   - Expected: runtime.is_runnable() equals `registry.is_runnable()`
   - Expected: runtime.detail equals `registry.detail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps runtime and registry probe semantics aligned")
val runtime = probe_riscv_external_formal()
val registry = probe_external_formal()
expect(runtime.is_runnable()).to_equal(registry.is_runnable())
expect(runtime.detail).to_equal(registry.detail)
```

</details>

#### documents skip behavior when the external formal lane is not runnable

- documents skip behavior when the external formal lane is not runnable
   - Expected: report.status.to_text() equals `skip_missing_tool`
   - Expected: report.is_acceptable() is true
   - Expected: packet.is_skip() is true
   - Expected: packet.channel equals `exit_code`
   - Expected: verifier.verify(packet).is_ok() is true
   - Expected: report.is_runnable() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents skip behavior when the external formal lane is not runnable")
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

- verifies the lane result via the canonical exit-code packet path
   - Expected: packet.lane_id equals `l.lane_id`
   - Expected: packet.channel equals `exit_code`
   - Expected: verifier.verify(packet).is_ok() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies the lane result via the canonical exit-code packet path")
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

- runs the external formal bundle when tools are available
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the external formal bundle when tools are available")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0aa4022249ea678cbdfaf2c0f2043cf87e6164fd6b6bffc8ac2a5b3ddb8b3e39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0aa4022249ea678cbdfaf2c0f2043cf87e6164fd6b6bffc8ac2a5b3ddb8b3e39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0aa4022249ea678cbdfaf2c0f2043cf87e6164fd6b6bffc8ac2a5b3ddb8b3e39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/hardware/rv32_external_formal_harness_spec.spl
mirror: doc/06_spec/03_system/hardware/rv32_external_formal_harness_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/rv32_external_formal_harness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/rv32_external_formal_harness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/rv32_external_formal_harness_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates the harness bundle files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/rv32_external_formal_harness_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes a harness with rv32i_core assertions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/rv32_external_formal_harness_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes an sby file tied to the rv32 rtl set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
