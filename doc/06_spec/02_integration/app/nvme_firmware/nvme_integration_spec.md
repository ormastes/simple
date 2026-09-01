# nvme_integration_spec

> NVMe firmware + emulator end-to-end integration scenarios.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_integration_spec

NVMe firmware + emulator end-to-end integration scenarios.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVME-INTEG-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md |
| Design | N/A |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/02_integration/app/nvme_firmware/nvme_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe firmware + emulator end-to-end integration scenarios.

The integration tier joins the firmware layers (HIL → FTL → FIL) and the NVMe
controller (admin + IO queues) end-to-end, and joins the host/device emulator over
its memcpy/DMA seam. The scenario mains live under
examples/09_embedded/simpleos_nvme_fw/ and cannot be bare-imported from test/
(cross-example import is unsupported), so the tier drives each scenario through the
real CLI (`bin/simple run`) as a subprocess and asserts the operator-visible
end-to-end PASS evidence. Run:
`bin/simple test test/02_integration/app/nvme_firmware/nvme_integration_spec.spl`.

## Scenarios

### NVMe firmware HIL/FTL/FIL end-to-end integration

#### round-trips a host command through HIL, FTL, and FIL to NAND and back

- round-trips a host command through HIL, FTL, and FIL to NAND and back
- Run the firmware end-to-end simulation through the CLI
   - Expected: code equals `0`
- The joined HIL/FTL/FIL scenario reports overall end-to-end PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("round-trips a host command through HIL, FTL, and FIL to NAND and back")
step("Run the firmware end-to-end simulation through the CLI")
val (out, err, code) = _run(FW + "/sim_main.spl")
expect(code).to_equal(0)

step("The joined HIL/FTL/FIL scenario reports overall end-to-end PASS")
expect(out).to_contain("ALL END-TO-END CHECKS PASS")
```

</details>

### NVMe firmware NVMe controller admin+IO-queue integration

#### processes admin and multi IO-queue traffic end-to-end through the controller

- processes admin and multi IO-queue traffic end-to-end through the controller
- Run the NVMe controller end-to-end scenario through the CLI
   - Expected: code equals `0`
- The controller admin + IO-queue scenario reports overall end-to-end PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("processes admin and multi IO-queue traffic end-to-end through the controller")
step("Run the NVMe controller end-to-end scenario through the CLI")
val (out, err, code) = _run(FW + "/nvme_main.spl")
expect(code).to_equal(0)

step("The controller admin + IO-queue scenario reports overall end-to-end PASS")
expect(out).to_contain("ALL NVME CONTROLLER E2E CHECKS PASS")
```

</details>

### NVMe host/device emulator integration

#### joins the host and device emulator over the memcpy/DMA seam end-to-end

- joins the host and device emulator over the memcpy/DMA seam end-to-end
- Run the host/device emulator end-to-end demo through the CLI
   - Expected: code equals `0`
- The joined host/device emulator scenario reports overall end-to-end PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("joins the host and device emulator over the memcpy/DMA seam end-to-end")
step("Run the host/device emulator end-to-end demo through the CLI")
val (out, err, code) = _run(EMU + "/nvme_emu_main.spl")
expect(code).to_equal(0)

step("The joined host/device emulator scenario reports overall end-to-end PASS")
expect(out).to_contain("EMU E2E PASS")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md`
- **Research:** `doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f5af82d4544c617dbc1159b991de035df16592651f2474d5a58bdbe3aac15b13`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f5af82d4544c617dbc1159b991de035df16592651f2474d5a58bdbe3aac15b13`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f5af82d4544c617dbc1159b991de035df16592651f2474d5a58bdbe3aac15b13`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/app/nvme_firmware/nvme_integration_spec.spl
mirror: doc/06_spec/02_integration/app/nvme_firmware/nvme_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/nvme_firmware/nvme_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/nvme_firmware/nvme_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/nvme_firmware/nvme_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/nvme_firmware/nvme_integration_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a host command through HIL, FTL, and FIL to NAND and back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/nvme_firmware/nvme_integration_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'processes admin and multi IO-queue traffic end-to-end through the controller' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/nvme_firmware/nvme_integration_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins the host and device emulator over the memcpy/DMA seam end-to-end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
