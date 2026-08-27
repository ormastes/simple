# rv32_nvme_host_axi_mmio_spec

> RV32 NVMe host AXI/MMIO transport contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv32_nvme_host_axi_mmio_spec

RV32 NVMe host AXI/MMIO transport contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

RV32 NVMe host AXI/MMIO transport contract.

This executable spec runs the endpoint protocol gate, the real resident RV32
firmware-in-loop AXI gate, and the QEMU command-parity gate. GHDL proves MMIO,
queue/payload DMA, CQE/IRQ, and RAM-NAND recovery. QEMU proves the same firmware
command sequence through a GDB-driven guest-RAM mailbox; it does not claim AXI
or IRQ transport. Physical H2 remains open.

## Scenarios

### RV32 NVMe host AXI/MMIO contract

### H1 endpoint execution

<details>
<summary>Advanced: should pass endpoint and real firmware-in-loop AXI RAM checks</summary>

#### should pass endpoint and real firmware-in-loop AXI RAM checks

</details>

#### should pass real firmware command parity in QEMU

- should pass real firmware command parity in QEMU
- Run the resident RV32 firmware with a GDB-driven host mailbox
   - Expected: code equals `0`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should pass real firmware command parity in QEMU")
step("Run the resident RV32 firmware with a GDB-driven host mailbox")
val (out, err, code) = process_run("/bin/sh", [QEMU_RUNNER])
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("RV32_NVME_QEMU_HOST_PASS write=erase+program recovery=1 refresh=2 remap=1 reads=4")
expect(out).to_contain("STATUS: PASS rv32-nvme-qemu-host-parity firmware=real transport=qemu-gdb-mailbox")
```

</details>

#### should retain plain and garbage-filled K26 boot evidence separately

- should retain plain and garbage-filled K26 boot evidence separately
- Check that the K26 rehearsal cannot overwrite its negative control
   - Expected: source does not contain `tb_rv32_k26_ddr_boot.vhd" 2>&1)" || true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain plain and garbage-filled K26 boot evidence separately")
step("Check that the K26 rehearsal cannot overwrite its negative control")
val source = _source(K26_RUNNER)
expect(source).to_contain("build/ghdl/rv32_k26_ddr_boot_garbage")
expect(source).to_contain("EVIDENCE_DIR=\"${{WORK_DIR:-$DEFAULT_WORK_DIR}}\"")
expect(source).to_contain("mktemp -d \"$EVIDENCE_DIR/run.XXXXXX\"")
expect(source).to_contain("K26_GARBAGE_FILL=%s")
expect(source).to_contain("simulation exited with status $sim_status")
expect(source.contains("tb_rv32_k26_ddr_boot.vhd\" 2>&1)\" || true")).to_equal(false)
```

</details>

### REQ-001: NVMe register aperture

#### should retain the standard register offsets

- should retain the standard register offsets
- Read the shared NVMe register ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain the standard register offsets")
step("Read the shared NVMe register ABI")
val source = _source(TYPES)
expect(source).to_contain("NVME_REG_CAP")
expect(source).to_contain("NVME_REG_VS")
expect(source).to_contain("NVME_REG_CC")
expect(source).to_contain("NVME_REG_CSTS")
```

</details>

#### should retain queue base and interrupt register definitions

- should retain queue base and interrupt register definitions
- Check queue and interrupt register names


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain queue base and interrupt register definitions")
step("Check queue and interrupt register names")
val source = _source(TYPES)
expect(source).to_contain("NVME_REG_INTMS")
expect(source).to_contain("NVME_REG_INTMC")
expect(source).to_contain("NVME_REG_AQA")
expect(source).to_contain("NVME_REG_ASQ")
expect(source).to_contain("NVME_REG_ACQ")
```

</details>

#### should require a host MMIO endpoint rather than the debug slave

- should require a host MMIO endpoint rather than the debug slave
- Check the architecture ownership boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require a host MMIO endpoint rather than the debug slave")
step("Check the architecture ownership boundary")
val source = _source(ARCH)
expect(source).to_contain("NVMe register and doorbell AXI-Lite slave")
expect(_source(GUIDE)).to_contain("not a NAND MMIO register device")
```

</details>

### REQ-002: reset and enable

#### should retain the CC and CSTS enable bits

- should retain the CC and CSTS enable bits
- Check controller state bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain the CC and CSTS enable bits")
step("Check controller state bits")
val source = _source(TYPES)
expect(source).to_contain("CC_EN")
expect(source).to_contain("CSTS_RDY")
expect(source).to_contain("CSTS_CFS")
```

</details>

#### should require NVM CSS and fixed queue entry sizes

- should require NVM CSS and fixed queue entry sizes
- Check the selected controller configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require NVM CSS and fixed queue entry sizes")
step("Check the selected controller configuration")
val source = _source(TYPES)
expect(source).to_contain("CC_CSS_NVM")
expect(source).to_contain("CC_IOSQES_64")
expect(source).to_contain("CC_IOCQES_16")
```

</details>

#### should fail closed on unvalidated controller state

- should fail closed on unvalidated controller state
- Check the fatal-state design


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail closed on unvalidated controller state")
step("Check the fatal-state design")
expect(_source(ARCH)).to_contain("invalid configuration sets a fatal status")
expect(_source(REQUIREMENTS)).to_contain("CSTS.CFS=1")
```

</details>

### REQ-003: queue and doorbells

#### should derive the doorbell stride from DSTRD

- should derive the doorbell stride from DSTRD
- Read the existing doorbell arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should derive the doorbell stride from DSTRD")
step("Read the existing doorbell arithmetic")
val source = _source(QUEUES)
expect(source).to_contain("4u32 << dstrd")
expect(source).to_contain("NVME_DOORBELL_BASE_OFFSET")
```

</details>

#### should constrain the first host queue pair

- should constrain the first host queue pair
- Check the selected queue scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should constrain the first host queue pair")
step("Check the selected queue scope")
val source = _source(REQUIREMENTS)
expect(source).to_contain("qid 0 and I/O qid 1")
expect(source).to_contain("depths 2..16")
```

</details>

#### should reject unaligned queue resources

- should reject unaligned queue resources
- Check queue resource validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject unaligned queue resources")
step("Check queue resource validation")
val source = _source(QUEUES)
expect(source).to_contain("nvme-queue-sq-phys-unaligned")
expect(source).to_contain("nvme-queue-cq-phys-unaligned")
```

</details>

### REQ-004: host-owned DMA

#### should require host SQE and CQE widths

- should require host SQE and CQE widths
- Check the fixed queue entry ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require host SQE and CQE widths")
step("Check the fixed queue entry ABI")
val source = _source(TYPES)
expect(source).to_contain("SQE_SIZE")
expect(source).to_contain("CQE_SIZE")
expect(source).to_contain("64 bytes")
```

</details>

#### should require DMA activity in transport evidence

- should require DMA activity in transport evidence
- Check the transport evidence requirements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require DMA activity in transport evidence")
step("Check the transport evidence requirements")
val source = _source(REQUIREMENTS)
expect(source).to_contain("queue-memory reads/writes")
expect(source).to_contain("DMA data movement")
expect(source).to_contain("interrupt assertion")
```

</details>

#### should exclude internally generated commands

- should exclude internally generated commands
- Check the host ownership rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should exclude internally generated commands")
step("Check the host ownership rule")
expect(_source(ARCH)).to_contain("internal selftest submission")
expect(_source(REQUEST)).to_contain("internal self-test")
```

</details>

### REQ-005: command floor

#### should list the selected admin commands

- should list the selected admin commands
- Check the command floor


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should list the selected admin commands")
step("Check the command floor")
val source = _source(REQUIREMENTS)
expect(source).to_contain("Identify")
expect(source).to_contain("Create CQ")
expect(source).to_contain("Create SQ")
```

</details>

#### should list the selected IO commands

- should list the selected IO commands
- Check data-path commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should list the selected IO commands")
step("Check data-path commands")
val source = _source(REQUIREMENTS)
expect(source).to_contain("Read")
expect(source).to_contain("Write")
expect(source).to_contain("Flush")
```

</details>

#### should require read-after-write payload equality

- should require read-after-write payload equality
- Check end-to-end payload acceptance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require read-after-write payload equality")
step("Check end-to-end payload acceptance")
expect(_source(REQUIREMENTS)).to_contain("exact host buffer contents")
expect(_source(DESIGN)).to_contain("4-byte NAND payload")
```

</details>

### REQ-006: fail-closed validation

#### should constrain the initial PRP contract

- should constrain the initial PRP contract
- Check PRP scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should constrain the initial PRP contract")
step("Check PRP scope")
val source = _source(REQUIREMENTS)
expect(source).to_contain("dword-aligned PRP1")
expect(source).to_contain("reject unsupported PRP2")
```

</details>

#### should reject invalid command inputs without media mutation

- should reject invalid command inputs without media mutation
- Check negative command behavior


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject invalid command inputs without media mutation")
step("Check negative command behavior")
expect(_source(REQUIREMENTS)).to_contain("shall not partially mutate media")
expect(_source(DESIGN)).to_contain("leave media unchanged")
```

</details>

#### should stop DMA on fatal state

- should stop DMA on fatal state
- Check fatal-state containment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should stop DMA on fatal state")
step("Check fatal-state containment")
expect(_source(ARCH)).to_contain("stop DMA")
expect(_source(DESIGN)).to_contain("Fatal")
```

</details>

### REQ-007: NAND policy integration

#### should retain the existing recovery evidence source

- should retain the existing recovery evidence source
- Read the existing RAM-NAND system spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain the existing recovery evidence source")
step("Read the existing RAM-NAND system spec")
val source = _source(NAND_SPEC)
expect(source).to_contain("NAND PREVENT PASS")
expect(source).to_contain("NAND RECOVERY PASS")
```

</details>

#### should route host commands into the existing policy

- should route host commands into the existing policy
- Check backend ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should route host commands into the existing policy")
step("Check backend ownership")
expect(_source(ARCH)).to_contain("existing RAM-NAND policy")
expect(_source(REQUIREMENTS)).to_contain("backend effects")
```

</details>

#### should retain FCR and remap as backend behavior

- should retain FCR and remap as backend behavior
- Check recovery policy terms


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain FCR and remap as backend behavior")
step("Check recovery policy terms")
val source = _source(REQUEST)
expect(source).to_contain("FCR")
expect(source).to_contain("alternate-slot recovery")
```

</details>

### REQ-008: observable evidence

#### should require MMIO, DMA, and IRQ trace evidence

- should require MMIO, DMA, and IRQ trace evidence
- Check the evidence matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require MMIO, DMA, and IRQ trace evidence")
step("Check the evidence matrix")
val source = _source(DESIGN)
expect(source).to_contain("register reads/writes")
expect(source).to_contain("payload DMA reads/writes")
expect(source).to_contain("IRQ assert/ack transitions")
```

</details>

#### should require completion and recovery markers

- should require completion and recovery markers
- Check retained artifact requirements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require completion and recovery markers")
step("Check retained artifact requirements")
expect(_source(REQUIREMENTS)).to_contain("completion consumption")
expect(_source(DESIGN)).to_contain("recovery, prevention, and alternate-remap counters")
```

</details>

#### should distinguish GHDL firmware closure from remaining targets

- should distinguish GHDL firmware closure from remaining targets
- Check the current test status


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should distinguish GHDL firmware closure from remaining targets")
step("Check the current test status")
expect(_source(DESIGN)).to_contain("resident RV32")
expect(_source(GUIDE)).to_contain("host-driven NVMe MMIO")
```

</details>

### REQ-009: profile parity

#### should retain explicit simulator and OpenSSD profiles

- should retain explicit simulator and OpenSSD profiles
- Read the profile table


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain explicit simulator and OpenSSD profiles")
step("Read the profile table")
val source = _source(TARGETS)
expect(source).to_contain("TARGET_SIMPLE_SIM")
expect(source).to_contain("TARGET_OPENSSD_2CH8WAY")
expect(source).to_contain("TARGET_OPENSSD_8CH8WAY")
```

</details>

#### should require the same host contract across H1 targets

- should require the same host contract across H1 targets
- Check profile parity wording


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the same host contract across H1 targets")
step("Check profile parity wording")
expect(_source(REQUIREMENTS)).to_contain("same host-driven contract")
expect(_source(ARCH)).to_contain("QEMU/RAM-NAND")
```

</details>

#### should fail closed for unknown profiles

- should fail closed for unknown profiles
- Check target selection failure behavior


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail closed for unknown profiles")
step("Check target selection failure behavior")
expect(_source(TARGETS)).to_contain("TARGET_INVALID")
expect(_source(TARGETS)).to_contain("unknown fails closed")
```

</details>

### REQ-010: H1 and H2 boundary

#### should label H1 as software or FPGA-model evidence

- should label H1 as software or FPGA-model evidence
- Check evidence-level labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should label H1 as software or FPGA-model evidence")
step("Check evidence-level labels")
expect(_source(REQUIREMENTS)).to_contain("H1")
expect(_source(ARCH)).to_contain("H1 FPGA-model evidence")
```

</details>

#### should keep PCIe and OpenSSD silicon in H2

- should keep PCIe and OpenSSD silicon in H2
- Check excluded claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep PCIe and OpenSSD silicon in H2")
step("Check excluded claims")
val source = _source(REQUIREMENTS)
expect(source).to_contain("PCIe enumeration")
expect(source).to_contain("OpenSSD silicon")
```

</details>

#### should preserve the QEMU transport and board acceptance boundary

- should preserve the QEMU transport and board acceptance boundary
- Check the operator guide claim boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the QEMU transport and board acceptance boundary")
step("Check the operator guide claim boundary")
val source = _source(GUIDE)
expect(source).to_contain("internal selftest")
expect(source).to_contain("QEMU does not prove AXI, DMA, IRQ, PCIe, or board acceptance")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `96a84a1b5e4383b98245d308cb71dc60d02e02a05b3c5686ef1210ca20344ae4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96a84a1b5e4383b98245d308cb71dc60d02e02a05b3c5686ef1210ca20344ae4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96a84a1b5e4383b98245d308cb71dc60d02e02a05b3c5686ef1210ca20344ae4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **68/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.md (current)
findings: 15 blockers: 2
  narrative=100 structure=60 oracle=40
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=68; blocker cap makes effective=49
doc/06_spec/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 10 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:42:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should pass endpoint and real firmware-in-loop AXI RAM checks' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pass endpoint and real firmware-in-loop AXI RAM checks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pass real firmware command parity in QEMU' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pass real firmware command parity in QEMU' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain plain and garbage-filled K26 boot evidence separately' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain plain and garbage-filled K26 boot evidence separately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain the standard register offsets' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain the standard register offsets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain queue base and interrupt register definitions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/rv32_nvme_host_axi_mmio_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require a host MMIO endpoint rather than the debug slave' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
