# rv32_nvme_nand_read_level_spec

> Verifies the rv32 nvme nand read level behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv32_nvme_nand_read_level_spec

Verifies the rv32 nvme nand read level behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the rv32 nvme nand read level behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### RV32 NVMe RAM-backed NAND read-level policy

#### should model sensing, bounded read retry, prevention, and recovery

- Verify: should model sensing, bounded read retry, prevention, and recovery
- Inspect the pure RV32 NAND policy
- Verify the retained reference ladder and prevention threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32-NAND-001 REQ-RV32-NAND-002 REQ-RV32-NAND-003 REQ-RV32-NAND-004 REQ-RV32-NAND-005 REQ-RV32-NAND-006 REQ-RV32-NAND-007
step("Verify: should model sensing, bounded read retry, prevention, and recovery")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Inspect the pure RV32 NAND policy")
val source = file_read_text(LOGIC)
expect(source).to_contain("rv32_nand_sense_data")
expect(source).to_contain("rv32_nand_retry_reference")
expect(source).to_contain("rv32_nand_ecc_correctable")
expect(source).to_contain("rv32_nand_refresh_allowed")
expect(source).to_contain("rv32_nand_disturb_level")

step("Verify the retained reference ladder and prevention threshold")
expect(source).to_contain("return 128")
expect(source).to_contain("return 120")
expect(source).to_contain("return 112")
expect(source).to_contain("return 104")
expect(source).to_contain("return 136")
expect(source).to_contain("return 144")
expect(source).to_contain("return 152")
expect(source).to_contain("rv32_nand_prevention_read_limit")
```

</details>

#### should execute startup, queues, media operations, and RAM telemetry

- Verify: should execute startup, queues, media operations, and RAM telemetry
- Inspect the RV32-only volatile NAND RAM path
- Verify every required JTAG transcript marker is retained
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32-NAND-001 REQ-RV32-NAND-002 REQ-RV32-NAND-003 REQ-RV32-NAND-004 REQ-RV32-NAND-005 REQ-RV32-NAND-006 REQ-RV32-NAND-007
step("Verify: should execute startup, queues, media operations, and RAM telemetry")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Inspect the RV32-only volatile NAND RAM path")
val source = file_read_text(ENTRY)
expect(source).to_contain("_nandram_start")
expect(source).to_contain("_nand_ram_startup")
expect(source).to_contain("_nand_ram_erase")
expect(source).to_contain("_nand_ram_program")
expect(source).to_contain("_nand_ram_read")
expect(source).to_contain("_nand_ram_fcr")
expect(source).to_contain("_nand_ram_remap")
expect(source).to_contain("rv32_nand_ecc_decode")
expect(source).to_contain("_nand_ram_read()")
expect(source).to_contain("_nand_ram_reap_completion")
expect(source).to_contain("_nand_ram_delete_io_queue")
expect(source).to_contain("_nand_ram_submit_io")
expect(source).to_contain("_nand_ram_complete_io")
expect(source).to_contain("_nand_ram_store(64, 0xDEADBEEF)")
expect(source).to_contain("if _nand_ram_load(64) != 0:")
expect(source).to_contain("NAND EVIDENCE D1 U1 F5 C3 T1 M1 Q3 X2 S1 PASS")

step("Verify every required JTAG transcript marker is retained")
val (out, err, code) = _run("sh " + CHECK + " --self-test")
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(err).to_equal("")
expect(out).to_contain("STATUS: PASS rv32-nvme-nand-recovery self-test")
```

</details>

#### should retain fail-closed GHDL and FPGA execution modes

- Verify: should retain fail-closed GHDL and FPGA execution modes
- Inspect the canonical evidence runner


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32-NAND-001 REQ-RV32-NAND-002 REQ-RV32-NAND-003 REQ-RV32-NAND-004 REQ-RV32-NAND-005 REQ-RV32-NAND-006 REQ-RV32-NAND-007
step("Verify: should retain fail-closed GHDL and FPGA execution modes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Inspect the canonical evidence runner")
val source = file_read_text(CHECK)
val axi_source = file_read_text(AXI_CHECK)
val qemu_source = file_read_text(QEMU_CHECK)
expect(source).to_contain("--ghdl")
expect(source).to_contain("--fpga")
expect(source).to_contain("require_self_hosted")
expect(source).to_contain("SELF_HOSTED_BIN")
expect(source).to_contain("nvme_rv32_source_matched")
expect(source).to_contain("manifest.txt")
expect(source).to_contain("source_manifest_version=2")
expect(source).to_contain("jj log -r @")
expect(source).to_contain("logic*.spl")
expect(source).to_contain("exact-bram.log")
expect(source).to_contain("FW_ELF=\"$ROOT/build/nvme_fw_rv32.elf\"")
expect(source).to_contain("FW_ELF=\"$ROOT/build/nvme_fw_rv32.elf\" sh scripts/fpga/ghdl_rv32_nvme_bram_soc.shs")
expect(source).to_contain("GARBAGE_FILL=1 FW_ELF=\"$ROOT/build/nvme_fw_rv32.elf\"")
expect(source).to_contain("ghdl_rv32_nvme_axi_ram.shs")
expect(source).to_contain("GARBAGE_FILL=1")
expect(source).to_contain("nvme_rv32_bram_soc/clean/sim.log")
expect(source).to_contain("nvme_rv32_bram_soc/garbage/sim.log")
expect(source).to_contain(">>\"$evidence/manifest.txt\"")
expect(source).to_contain("read_rv32_tiny_bram_obs.shs transcript")
expect(source).to_contain("sha256sum")
expect(axi_source).to_contain("SIM_LOG=\"$EVIDENCE_DIR/sim.log\"")
expect(axi_source).to_contain("WORK_DIR=\"$EVIDENCE_DIR\"")
expect(axi_source).to_contain("firmware .nandram size is $trace_bytes bytes, expected 256")
expect(qemu_source).to_contain("missing _nandram_end")
expect(qemu_source).to_contain("fail \"invalid .nandram size\"")
```

</details>

#### should execute the production NAND path on both GHDL cores

- Verify: should execute the production NAND path on both GHDL cores
- Build the RV32 firmware and run clean plus garbage-filled GHDL
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32-NAND-001 REQ-RV32-NAND-002 REQ-RV32-NAND-003 REQ-RV32-NAND-004 REQ-RV32-NAND-005 REQ-RV32-NAND-006 REQ-RV32-NAND-007
step("Verify: should execute the production NAND path on both GHDL cores")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the RV32 firmware and run clean plus garbage-filled GHDL")
val (out, err, code) = _run("sh " + CHECK + " --ghdl")
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(err).to_equal("")
expect(out).to_contain("STATUS: PASS rv32-nvme-nand-recovery ghdl")
expect(out).to_contain("NAND EVIDENCE D1 U1 F5 C3 T1 M1 Q3 X2 S1 PASS")
```

</details>

#### should execute prevention and recovery through AXI RAM

- Verify: should execute prevention and recovery through AXI RAM
- Run the RV32 firmware with NAND state transported through full AXI4
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32-NAND-001 REQ-RV32-NAND-002 REQ-RV32-NAND-003 REQ-RV32-NAND-004 REQ-RV32-NAND-005 REQ-RV32-NAND-006 REQ-RV32-NAND-007
step("Verify: should execute prevention and recovery through AXI RAM")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Run the RV32 firmware with NAND state transported through full AXI4")
val (out, err, code) = _run("sh " + AXI_CHECK)
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(err).to_equal("")
expect(out).to_contain("NAND PREVENT PASS")
expect(out).to_contain("NAND RECOVERY PASS")
expect(out).to_contain("K26_TRACE_READS=")
expect(out).to_contain("K26_TRACE_WRITES=")
expect(out).to_contain("RV32_NVME_AXI_RAM_PASS")
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cc7c231a7becc006570bc91637232f1476d44902f88bafa6d46dcef518256a62`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cc7c231a7becc006570bc91637232f1476d44902f88bafa6d46dcef518256a62`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cc7c231a7becc006570bc91637232f1476d44902f88bafa6d46dcef518256a62`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model sensing, bounded read retry, prevention, and recovery' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute startup, queues, media operations, and RAM telemetry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.spl:93:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain fail-closed GHDL and FPGA execution modes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.spl:127:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute the production NAND path on both GHDL cores' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/rv32_nvme_nand_read_level_spec.spl:138:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute prevention and recovery through AXI RAM' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
