# Remote Baremetal Lane Status System Spec

> 1. fallback result channel: Some

<!-- sdn-diagram:id=remote_baremetal_lane_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_baremetal_lane_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_baremetal_lane_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_baremetal_lane_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Baremetal Lane Status System Spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/remote_baremetal_lane_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#
#

## Scenarios

### LaneDescriptor

#### creates a descriptor with all fields

1. fallback result channel: Some
   - Expected: lane.lane_id equals `qemu_rv32`
   - Expected: lane.target_arch equals `riscv32`
   - Expected: lane.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = LaneDescriptor(
    lane_id: "qemu_rv32",
    target_arch: "riscv32",
    adapter_kind: AdapterKind.qemu_gdb,
    proof_class: ProofClass.compiled,
    primary_result_channel: ResultChannelKind.semihost_text,
    fallback_result_channel: Some(ResultChannelKind.exit_code),
    authoritative_spec_path: "test/some_spec.spl",
    status: LaneStatus.stable
)
expect(lane.lane_id).to_equal("qemu_rv32")
expect(lane.target_arch).to_equal("riscv32")
expect(lane.is_authoritative()).to_equal(true)
```

</details>

#### formats to_text correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = LaneDescriptor(
    lane_id: "qemu_rv32_semihost",
    target_arch: "riscv32",
    adapter_kind: AdapterKind.qemu_gdb,
    proof_class: ProofClass.compiled,
    primary_result_channel: ResultChannelKind.semihost_text,
    fallback_result_channel: nil,
    authoritative_spec_path: "",
    status: LaneStatus.stable
)
val text_repr = lane.to_text()
expect(text_repr).to_contain("qemu_rv32_semihost")
expect(text_repr).to_contain("riscv32")
```

</details>

#### classifies stable lanes as authoritative

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = LaneDescriptor(
    lane_id: "stable_lane",
    target_arch: "riscv32",
    adapter_kind: AdapterKind.qemu_gdb,
    proof_class: ProofClass.compiled,
    primary_result_channel: ResultChannelKind.semihost_text,
    fallback_result_channel: nil,
    authoritative_spec_path: "",
    status: LaneStatus.stable
)
expect(lane.is_authoritative()).to_equal(true)
```

</details>

#### classifies in_progress lanes as non-authoritative

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = LaneDescriptor(
    lane_id: "wip_lane",
    target_arch: "arm32",
    adapter_kind: AdapterKind.openocd_gdb,
    proof_class: ProofClass.structural,
    primary_result_channel: ResultChannelKind.register_readback,
    fallback_result_channel: nil,
    authoritative_spec_path: "",
    status: LaneStatus.in_progress
)
expect(lane.is_authoritative()).to_equal(false)
```

</details>

#### treats host-aware lanes as authoritative when the lane contract is satisfied

1. fallback result channel: Some
   - Expected: lane.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = LaneDescriptor(
    lane_id: "host_lane",
    target_arch: "arm32",
    adapter_kind: AdapterKind.trace32,
    proof_class: ProofClass.compiled,
    primary_result_channel: ResultChannelKind.debugger_console,
    fallback_result_channel: Some(ResultChannelKind.register_readback),
    authoritative_spec_path: "test/system/t32_terminal_power_remote_spec.spl",
    status: LaneStatus.host_aware
)
expect(lane.is_authoritative()).to_equal(true)
```

</details>

### CapabilityReport

#### creates ready reports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = CapabilityReport.ready("test_lane", "qemu-system-riscv32")
expect(report.is_runnable()).to_equal(true)
expect(report.is_acceptable()).to_equal(true)
```

</details>

#### creates skip_tool reports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = CapabilityReport.skip_tool("test_lane", "missing_tool")
expect(report.is_runnable()).to_equal(false)
expect(report.is_acceptable()).to_equal(true)
```

</details>

#### creates failed reports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = CapabilityReport.failed("test_lane", "critical error")
expect(report.is_runnable()).to_equal(false)
expect(report.is_acceptable()).to_equal(false)
```

</details>

#### formats report text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = CapabilityReport.ready("my_lane", "tool_name")
val text_repr = report.to_text()
expect(text_repr).to_contain("my_lane")
expect(text_repr).to_contain("ready")
```

</details>

### ResultPacket

#### creates semihost packets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packet = ResultPacket.from_semihost("test_lane", "PASS: all tests passed", 100)
expect(packet.is_pass()).to_equal(true)
```

</details>

#### creates register packets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pass_packet = ResultPacket.from_register("test_lane", 0, 50)
expect(pass_packet.is_pass()).to_equal(true)
val fail_packet = ResultPacket.from_register("test_lane", 1, 50)
expect(fail_packet.is_pass()).to_equal(false)
```

</details>

#### creates exit code packets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packet = ResultPacket.from_exit_code("test_lane", 0, "", 75)
expect(packet.is_pass()).to_equal(true)
```

</details>

#### creates skipped packets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packet = ResultPacket.skipped("test_lane", "exit_code", "missing toolchain", 5)
expect(packet.is_skip()).to_equal(true)
expect(packet.is_pass()).to_equal(false)
expect(packet.to_text()).to_contain("SKIP")
```

</details>

### ResultVerifier

#### verifies default pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verifier = ResultVerifier.default_pass()
val packet = ResultPacket.from_exit_code("test_lane", 0, "", 10)
val result = verifier.verify(packet)
expect(result.is_ok()).to_equal(true)
```

</details>

#### rejects failed packets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verifier = ResultVerifier.default_pass()
val packet = ResultPacket.from_exit_code("test_lane", 1, "", 10)
val result = verifier.verify(packet)
expect(result.is_err()).to_equal(true)
```

</details>

#### checks output patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verifier = ResultVerifier.with_output(["PASS"])
val packet = ResultPacket.from_semihost("test_lane", "PASS: all tests passed", 10)
val result = verifier.verify(packet)
expect(result.is_ok()).to_equal(true)
```

</details>

#### accepts skipped packets when configured

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verifier = ResultVerifier.allow_skip()
val packet = ResultPacket.skipped("test_lane", "exit_code", "missing toolchain", 5)
val result = verifier.verify(packet)
expect(result.is_ok()).to_equal(true)
```

</details>

### LaneRegistry
_The default registry is the source of truth for public lane classification._

#### contains exactly 12 lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
expect(registry.all().len()).to_equal(12)
```

</details>

#### has 3 stable lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
expect(registry.stable_lanes().len()).to_equal(3)
```

</details>

#### has 5 host-aware lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
expect(registry.host_aware_lanes().len()).to_equal(5)
```

</details>

#### has 3 transport-only lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
expect(registry.transport_only_lanes().len()).to_equal(3)
```

</details>

#### has no in-progress lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
expect(registry.in_progress_lanes().len()).to_equal(0)
```

</details>

#### has 1 publicly excluded lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
expect(registry.excluded_public_lanes().len()).to_equal(1)
```

</details>

#### has 8 authoritative lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
expect(registry.authoritative_lanes().len()).to_equal(8)
```

</details>

#### assigns concrete result channels to every authoritative lane

1. Some
   - Expected: l.primary_result_channel equals `ResultChannelKind.semihost_text`
   - Expected: l.fallback_result_channel equals `Some(ResultChannelKind.exit_code)`
2. Some
   - Expected: l.primary_result_channel equals `ResultChannelKind.exit_code`
3. Some
   - Expected: l.primary_result_channel equals `ResultChannelKind.register_readback`
   - Expected: l.fallback_result_channel equals `Some(ResultChannelKind.ram_sentinel)`
4. Some
   - Expected: l.primary_result_channel equals `ResultChannelKind.debugger_console`
   - Expected: l.fallback_result_channel equals `Some(ResultChannelKind.register_readback)`
5. Some
   - Expected: l.primary_result_channel equals `ResultChannelKind.ram_sentinel`
   - Expected: l.fallback_result_channel equals `Some(ResultChannelKind.register_readback)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lanes = registry.authoritative_lanes()
for lane in lanes:
    expect(lane.authoritative_spec_path.len()).to_be_greater_than(0)

val qemu_rv32 = registry.find("qemu_rv32_semihost")
match qemu_rv32:
    Some(l):
        expect(l.primary_result_channel).to_equal(ResultChannelKind.semihost_text)
        expect(l.fallback_result_channel).to_equal(Some(ResultChannelKind.exit_code))
    nil: expect(false).to_equal(true)

val direct_boot = registry.find("x86_64_direct_boot")
match direct_boot:
    Some(l):
        expect(l.primary_result_channel).to_equal(ResultChannelKind.exit_code)
        expect(l.fallback_result_channel).to_be_nil()
    nil: expect(false).to_equal(true)

val openocd = registry.find("stm32h7_openocd")
match openocd:
    Some(l):
        expect(l.primary_result_channel).to_equal(ResultChannelKind.register_readback)
        expect(l.fallback_result_channel).to_equal(Some(ResultChannelKind.ram_sentinel))
    nil: expect(false).to_equal(true)

val trace32 = registry.find("stm32h7_trace32")
match trace32:
    Some(l):
        expect(l.primary_result_channel).to_equal(ResultChannelKind.debugger_console)
        expect(l.fallback_result_channel).to_equal(Some(ResultChannelKind.register_readback))
    nil: expect(false).to_equal(true)

val mailbox = registry.find("ghdl_rv32_mailbox")
match mailbox:
    Some(l):
        expect(l.primary_result_channel).to_equal(ResultChannelKind.ram_sentinel)
        expect(l.fallback_result_channel).to_equal(Some(ResultChannelKind.register_readback))
    nil: expect(false).to_equal(true)
```

</details>

#### finds lanes by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("qemu_rv32_semihost")
match lane:
    Some(l): expect(l.lane_id).to_equal("qemu_rv32_semihost")
    nil: expect(false).to_equal(true)
```

</details>

#### uses the x86_64 boot spec for the direct boot lane

1. Some
   - Expected: l.status equals `LaneStatus.stable`
   - Expected: l.authoritative_spec_path equals `test/system/qemu/os/boot/x86_64_boot_qemu_spec.spl`
   - Expected: l.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("x86_64_direct_boot")
match lane:
    Some(l):
        expect(l.status).to_equal(LaneStatus.stable)
        expect(l.authoritative_spec_path).to_equal("test/system/qemu/os/boot/x86_64_boot_qemu_spec.spl")
        expect(l.is_authoritative()).to_equal(true)
    nil: expect(false).to_equal(true)
```

</details>

#### returns nil for unknown lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("nonexistent")
expect(lane).to_be_nil()
```

</details>

#### looks up ghdl_rv32_semihost as host_aware

1. Some
   - Expected: l.status equals `LaneStatus.host_aware`
   - Expected: l.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("ghdl_rv32_semihost")
match lane:
    Some(l):
        expect(l.status).to_equal(LaneStatus.host_aware)
        expect(l.is_authoritative()).to_equal(true)
    nil: expect(false).to_equal(true)
```

</details>

#### looks up ghdl_rv32_mailbox as host_aware

1. Some
   - Expected: l.status equals `LaneStatus.host_aware`
   - Expected: l.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("ghdl_rv32_mailbox")
match lane:
    Some(l):
        expect(l.status).to_equal(LaneStatus.host_aware)
        expect(l.is_authoritative()).to_equal(true)
    nil: expect(false).to_equal(true)
```

</details>

#### looks up riscv_external_formal as transport_only

1. Some
   - Expected: l.status equals `LaneStatus.transport_only`
   - Expected: l.adapter_kind equals `AdapterKind.external_formal`
   - Expected: l.is_authoritative() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("riscv_external_formal")
match lane:
    Some(l):
        expect(l.status).to_equal(LaneStatus.transport_only)
        expect(l.adapter_kind).to_equal(AdapterKind.external_formal)
        expect(l.is_authoritative()).to_equal(false)
    nil: expect(false).to_equal(true)
```

</details>

#### returns nil for removed ghdl_rv32_sim

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("ghdl_rv32_sim")
expect(lane).to_be_nil()
```

</details>

#### looks up fpga_jtag_zedboard as publicly excluded

1. Some
   - Expected: l.status equals `LaneStatus.excluded_public`
   - Expected: l.is_authoritative() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lane = registry.find("fpga_jtag_zedboard")
match lane:
    Some(l):
        expect(l.status).to_equal(LaneStatus.excluded_public)
        expect(l.is_authoritative()).to_equal(false)
    nil: expect(false).to_equal(true)
```

</details>

### LaneStatusReporter

#### generates text report

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reporter = LaneStatusReporter.new()
val report = reporter.report_text()
expect(report).to_contain("Stable Lanes")
expect(report).to_contain("Host-Aware")
expect(report).to_contain("Publicly Excluded Lanes")
expect(report).to_contain("stable and host-aware lanes are authoritative")
```

</details>

#### generates markdown report

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reporter = LaneStatusReporter.new()
val report = reporter.generate_matrix_markdown()
expect(report).to_contain("| Lane ID |")
expect(report).to_contain("| Authoritative |")
expect(report).to_contain("- **Authoritative**: 8 lanes (stable + host-aware)")
expect(report).to_contain("- **Publicly excluded**: 1 lanes")
```

</details>

#### generates SDN report

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reporter = LaneStatusReporter.new()
val report = reporter.report_sdn()
expect(report).to_contain("[lane_matrix]")
expect(report).to_contain("authoritative =")
```

</details>

### Probe infrastructure

#### detects available commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = probe_command("ls")
expect(found).to_equal(true)
```

</details>

#### detects missing commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = probe_command("nonexistent_tool_xyz")
expect(found).to_equal(false)
```

</details>

#### probes external formal capability cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = probe_external_formal()
expect(report.lane_id).to_equal("riscv_external_formal")
expect(report.is_acceptable()).to_equal(true)
expect(report.detail.len()).to_be_greater_than(0)
```

</details>

#### treats missing OpenOCD and TRACE32 tools as acceptable host-aware skips

1. Some
   - Expected: l.status equals `LaneStatus.host_aware`
   - Expected: report.status equals `CapabilityStatus.skip_missing_tool`
   - Expected: report.tool_name equals `openocd`
   - Expected: report.is_runnable() is false
   - Expected: report.is_acceptable() is true
2. Some
   - Expected: l.status equals `LaneStatus.host_aware`
   - Expected: report.status equals `CapabilityStatus.skip_missing_tool`
   - Expected: report.tool_name equals `t32rem`
   - Expected: report.is_runnable() is false
   - Expected: report.is_acceptable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()

val openocd_lane = registry.find("stm32h7_openocd")
match openocd_lane:
    Some(l):
        expect(l.status).to_equal(LaneStatus.host_aware)
        val report = probe_openocd_capability(false)
        expect(report.status).to_equal(CapabilityStatus.skip_missing_tool)
        expect(report.tool_name).to_equal("openocd")
        expect(report.is_runnable()).to_equal(false)
        expect(report.is_acceptable()).to_equal(true)
    nil: expect(false).to_equal(true)

val trace32_lane = registry.find("stm32h7_trace32")
match trace32_lane:
    Some(l):
        expect(l.status).to_equal(LaneStatus.host_aware)
        val report = probe_trace32_capability(false)
        expect(report.status).to_equal(CapabilityStatus.skip_missing_tool)
        expect(report.tool_name).to_equal("t32rem")
        expect(report.is_runnable()).to_equal(false)
        expect(report.is_acceptable()).to_equal(true)
    nil: expect(false).to_equal(true)
```

</details>

<details>
<summary>Advanced: probes all lanes without crashing</summary>

#### probes all lanes without crashing _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = LaneRegistry.default()
val lanes = registry.all()
var i = 0
while i < lanes.len():
    val lane = lanes[i]
    val report = probe_for_lane(lane)
    expect(report.is_acceptable()).to_equal(true)
    i = i + 1
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
