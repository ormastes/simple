# Remote Baremetal Lane Status System Spec

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#
#

## Scenarios

### LaneDescriptor

#### creates a descriptor with all fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a descriptor with all fields
   - Expected: lane.lane_id equals `qemu_rv32`
   - Expected: lane.target_arch equals `riscv32`
   - Expected: lane.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a descriptor with all fields")
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

- formats to_text correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats to_text correctly")
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

- classifies stable lanes as authoritative
   - Expected: lane.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies stable lanes as authoritative")
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

- classifies in_progress lanes as non-authoritative
   - Expected: lane.is_authoritative() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies in_progress lanes as non-authoritative")
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

- treats host-aware lanes as authoritative when the lane contract is satisfied
   - Expected: lane.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats host-aware lanes as authoritative when the lane contract is satisfied")
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

- creates ready reports
   - Expected: report.is_runnable() is true
   - Expected: report.is_acceptable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates ready reports")
val report = CapabilityReport.ready("test_lane", "qemu-system-riscv32")
expect(report.is_runnable()).to_equal(true)
expect(report.is_acceptable()).to_equal(true)
```

</details>

#### creates skip_tool reports

- creates skip_tool reports
   - Expected: report.is_runnable() is false
   - Expected: report.is_acceptable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates skip_tool reports")
val report = CapabilityReport.skip_tool("test_lane", "missing_tool")
expect(report.is_runnable()).to_equal(false)
expect(report.is_acceptable()).to_equal(true)
```

</details>

#### creates failed reports

- creates failed reports
   - Expected: report.is_runnable() is false
   - Expected: report.is_acceptable() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates failed reports")
val report = CapabilityReport.failed("test_lane", "critical error")
expect(report.is_runnable()).to_equal(false)
expect(report.is_acceptable()).to_equal(false)
```

</details>

#### formats report text

- formats report text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats report text")
val report = CapabilityReport.ready("my_lane", "tool_name")
val text_repr = report.to_text()
expect(text_repr).to_contain("my_lane")
expect(text_repr).to_contain("ready")
```

</details>

### ResultPacket

#### creates semihost packets

- creates semihost packets
   - Expected: packet.is_pass() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates semihost packets")
val packet = ResultPacket.from_semihost("test_lane", "PASS: all tests passed", 100)
expect(packet.is_pass()).to_equal(true)
```

</details>

#### creates register packets

- creates register packets
   - Expected: pass_packet.is_pass() is true
   - Expected: fail_packet.is_pass() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates register packets")
val pass_packet = ResultPacket.from_register("test_lane", 0, 50)
expect(pass_packet.is_pass()).to_equal(true)
val fail_packet = ResultPacket.from_register("test_lane", 1, 50)
expect(fail_packet.is_pass()).to_equal(false)
```

</details>

#### creates exit code packets

- creates exit code packets
   - Expected: packet.is_pass() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates exit code packets")
val packet = ResultPacket.from_exit_code("test_lane", 0, "", 75)
expect(packet.is_pass()).to_equal(true)
```

</details>

#### creates skipped packets

- creates skipped packets
   - Expected: packet.is_skip() is true
   - Expected: packet.is_pass() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates skipped packets")
val packet = ResultPacket.skipped("test_lane", "exit_code", "missing toolchain", 5)
expect(packet.is_skip()).to_equal(true)
expect(packet.is_pass()).to_equal(false)
expect(packet.to_text()).to_contain("SKIP")
```

</details>

### ResultVerifier

#### verifies default pass

- verifies default pass
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies default pass")
val verifier = ResultVerifier.default_pass()
val packet = ResultPacket.from_exit_code("test_lane", 0, "", 10)
val result = verifier.verify(packet)
expect(result.is_ok()).to_equal(true)
```

</details>

#### rejects failed packets

- rejects failed packets
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects failed packets")
val verifier = ResultVerifier.default_pass()
val packet = ResultPacket.from_exit_code("test_lane", 1, "", 10)
val result = verifier.verify(packet)
expect(result.is_err()).to_equal(true)
```

</details>

#### checks output patterns

- checks output patterns
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks output patterns")
val verifier = ResultVerifier.with_output(["PASS"])
val packet = ResultPacket.from_semihost("test_lane", "PASS: all tests passed", 10)
val result = verifier.verify(packet)
expect(result.is_ok()).to_equal(true)
```

</details>

#### accepts skipped packets when configured

- accepts skipped packets when configured
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts skipped packets when configured")
val verifier = ResultVerifier.allow_skip()
val packet = ResultPacket.skipped("test_lane", "exit_code", "missing toolchain", 5)
val result = verifier.verify(packet)
expect(result.is_ok()).to_equal(true)
```

</details>

### LaneRegistry
_The default registry is the source of truth for public lane classification._

#### contains exactly 12 lanes

- contains exactly 12 lanes
   - Expected: registry.all().len() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains exactly 12 lanes")
val registry = LaneRegistry.default()
expect(registry.all().len()).to_equal(12)
```

</details>

#### has 3 stable lanes

- has 3 stable lanes
   - Expected: registry.stable_lanes().len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has 3 stable lanes")
val registry = LaneRegistry.default()
expect(registry.stable_lanes().len()).to_equal(3)
```

</details>

#### has 5 host-aware lanes

- has 5 host-aware lanes
   - Expected: registry.host_aware_lanes().len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has 5 host-aware lanes")
val registry = LaneRegistry.default()
expect(registry.host_aware_lanes().len()).to_equal(5)
```

</details>

#### has 3 transport-only lanes

- has 3 transport-only lanes
   - Expected: registry.transport_only_lanes().len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has 3 transport-only lanes")
val registry = LaneRegistry.default()
expect(registry.transport_only_lanes().len()).to_equal(3)
```

</details>

#### has no in-progress lanes

- has no in-progress lanes
   - Expected: registry.in_progress_lanes().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has no in-progress lanes")
val registry = LaneRegistry.default()
expect(registry.in_progress_lanes().len()).to_equal(0)
```

</details>

#### has 1 publicly excluded lane

- has 1 publicly excluded lane
   - Expected: registry.excluded_public_lanes().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has 1 publicly excluded lane")
val registry = LaneRegistry.default()
expect(registry.excluded_public_lanes().len()).to_equal(1)
```

</details>

#### has 8 authoritative lanes

- has 8 authoritative lanes
   - Expected: registry.authoritative_lanes().len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has 8 authoritative lanes")
val registry = LaneRegistry.default()
expect(registry.authoritative_lanes().len()).to_equal(8)
```

</details>

#### assigns concrete result channels to every authoritative lane

- assigns concrete result channels to every authoritative lane
   - Expected: l.primary_result_channel equals `ResultChannelKind.semihost_text`
   - Expected: l.fallback_result_channel equals `Some(ResultChannelKind.exit_code)`
   - Expected: l.primary_result_channel equals `ResultChannelKind.exit_code`
   - Expected: l.primary_result_channel equals `ResultChannelKind.register_readback`
   - Expected: l.fallback_result_channel equals `Some(ResultChannelKind.ram_sentinel)`
   - Expected: l.primary_result_channel equals `ResultChannelKind.debugger_console`
   - Expected: l.fallback_result_channel equals `Some(ResultChannelKind.register_readback)`
   - Expected: l.primary_result_channel equals `ResultChannelKind.ram_sentinel`
   - Expected: l.fallback_result_channel equals `Some(ResultChannelKind.register_readback)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assigns concrete result channels to every authoritative lane")
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

- finds lanes by id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds lanes by id")
val registry = LaneRegistry.default()
val lane = registry.find("qemu_rv32_semihost")
match lane:
    Some(l): expect(l.lane_id).to_equal("qemu_rv32_semihost")
    nil: expect(false).to_equal(true)
```

</details>

#### uses the x86_64 boot spec for the direct boot lane

- uses the x86_64 boot spec for the direct boot lane
   - Expected: l.status equals `LaneStatus.stable`
   - Expected: l.authoritative_spec_path equals `test/system/qemu/os/boot/x86_64_boot_qemu_spec.spl`
   - Expected: l.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses the x86_64 boot spec for the direct boot lane")
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

- returns nil for unknown lanes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for unknown lanes")
val registry = LaneRegistry.default()
val lane = registry.find("nonexistent")
expect(lane).to_be_nil()
```

</details>

#### looks up ghdl_rv32_semihost as host_aware

- looks up ghdl_rv32_semihost as host_aware
   - Expected: l.status equals `LaneStatus.host_aware`
   - Expected: l.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("looks up ghdl_rv32_semihost as host_aware")
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

- looks up ghdl_rv32_mailbox as host_aware
   - Expected: l.status equals `LaneStatus.host_aware`
   - Expected: l.is_authoritative() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("looks up ghdl_rv32_mailbox as host_aware")
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

- looks up riscv_external_formal as transport_only
   - Expected: l.status equals `LaneStatus.transport_only`
   - Expected: l.adapter_kind equals `AdapterKind.external_formal`
   - Expected: l.is_authoritative() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("looks up riscv_external_formal as transport_only")
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

- returns nil for removed ghdl_rv32_sim


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for removed ghdl_rv32_sim")
val registry = LaneRegistry.default()
val lane = registry.find("ghdl_rv32_sim")
expect(lane).to_be_nil()
```

</details>

#### looks up fpga_jtag_zedboard as publicly excluded

- looks up fpga_jtag_zedboard as publicly excluded
   - Expected: l.status equals `LaneStatus.excluded_public`
   - Expected: l.is_authoritative() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("looks up fpga_jtag_zedboard as publicly excluded")
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

- generates text report


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates text report")
val reporter = LaneStatusReporter.new()
val report = reporter.report_text()
expect(report).to_contain("Stable Lanes")
expect(report).to_contain("Host-Aware")
expect(report).to_contain("Publicly Excluded Lanes")
expect(report).to_contain("stable and host-aware lanes are authoritative")
```

</details>

#### generates markdown report

- generates markdown report


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates markdown report")
val reporter = LaneStatusReporter.new()
val report = reporter.generate_matrix_markdown()
expect(report).to_contain("| Lane ID |")
expect(report).to_contain("| Authoritative |")
expect(report).to_contain("- **Authoritative**: 8 lanes (stable + host-aware)")
expect(report).to_contain("- **Publicly excluded**: 1 lanes")
```

</details>

#### generates SDN report

- generates SDN report


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates SDN report")
val reporter = LaneStatusReporter.new()
val report = reporter.report_sdn()
expect(report).to_contain("[lane_matrix]")
expect(report).to_contain("authoritative =")
```

</details>

### Probe infrastructure

#### detects available commands

- detects available commands
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects available commands")
val found = probe_command("ls")
expect(found).to_equal(true)
```

</details>

#### detects missing commands

- detects missing commands
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects missing commands")
val found = probe_command("nonexistent_tool_xyz")
expect(found).to_equal(false)
```

</details>

#### probes external formal capability cleanly

- probes external formal capability cleanly
   - Expected: report.lane_id equals `riscv_external_formal`
   - Expected: report.is_acceptable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("probes external formal capability cleanly")
val report = probe_external_formal()
expect(report.lane_id).to_equal("riscv_external_formal")
expect(report.is_acceptable()).to_equal(true)
expect(report.detail.len()).to_be_greater_than(0)
```

</details>

#### treats missing OpenOCD and TRACE32 tools as acceptable host-aware skips

- treats missing OpenOCD and TRACE32 tools as acceptable host-aware skips
   - Expected: l.status equals `LaneStatus.host_aware`
   - Expected: report.status equals `CapabilityStatus.skip_missing_tool`
   - Expected: report.tool_name equals `openocd`
   - Expected: report.is_runnable() is false
   - Expected: report.is_acceptable() is true
   - Expected: l.status equals `LaneStatus.host_aware`
   - Expected: report.status equals `CapabilityStatus.skip_missing_tool`
   - Expected: report.tool_name equals `t32rem`
   - Expected: report.is_runnable() is false
   - Expected: report.is_acceptable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats missing OpenOCD and TRACE32 tools as acceptable host-aware skips")
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

- probes all lanes without crashing
   - Expected: report.is_acceptable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("probes all lanes without crashing")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d7124dc970535b4dcd153edf14de56da06821bdaad6f4d044fcaac89dff4480`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d7124dc970535b4dcd153edf14de56da06821bdaad6f4d044fcaac89dff4480`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d7124dc970535b4dcd153edf14de56da06821bdaad6f4d044fcaac89dff4480`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/hardware/remote_baremetal_lane_status_spec.spl
mirror: doc/06_spec/03_system/hardware/remote_baremetal_lane_status_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/remote_baremetal_lane_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/remote_baremetal_lane_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/remote_baremetal_lane_status_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/hardware/remote_baremetal_lane_status_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a descriptor with all fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/remote_baremetal_lane_status_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats to_text correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/remote_baremetal_lane_status_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies stable lanes as authoritative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
