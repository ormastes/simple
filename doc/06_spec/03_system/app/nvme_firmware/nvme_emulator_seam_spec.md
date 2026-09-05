# nvme_emulator_seam_spec

> NVMe host/device emulator — end-to-end system scenario + Lean4 verification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_emulator_seam_spec

NVMe host/device emulator — end-to-end system scenario + Lean4 verification.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVME-EMU-001 |
| Category | Hardware |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/hardware/nvme_fw_emulated_nand_plan.md |
| Design | N/A |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/03_system/app/nvme_firmware/nvme_emulator_seam_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe host/device emulator — end-to-end system scenario + Lean4 verification.

The pure-Simple emulator (examples/09_embedded/simpleos_nvme_fw/emu/) splits into a
HOST interface and a DEVICE interface that exchange data only across a SETTABLE
memcpy/DMA seam, over an ONFI NAND (2 channels x 2 banks x 2 planes x 2 blocks),
custom-typed, with Lean4-verified resource and correctness invariants.

The emulator modules live under examples/ and cannot be bare-imported from test/
(cross-example import is unsupported), so this scenario drives them through the
real CLI (`bin/simple run`) and the Lean toolchain (`lean`) as subprocesses, and
asserts the operator-visible PASS evidence — exactly what the generated manual
shows. Run: `bin/simple test test/03_system/app/nvme_firmware/nvme_emulator_seam_spec.spl`.

## Scenarios

### NVMe emulator: host/device memcpy seam over ONFI NAND

#### round-trips the full host-to-device-to-host path on both NAND channels

- round-trips the full host-to-device-to-host path on both NAND channels
- Run the emulator end-to-end demo through the CLI
   - Expected: code equals `0`
- Host writes LBA 5, the device stores it in NAND, the host reads it back intact
- A second LBA lands in a different NAND channel and round-trips independently
- The end-to-end scenario reports overall PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("round-trips the full host-to-device-to-host path on both NAND channels")
step("Run the emulator end-to-end demo through the CLI")
val (out, err, code) = _run(EMU + "/nvme_emu_main.spl")
expect(code).to_equal(0)

step("Host writes LBA 5, the device stores it in NAND, the host reads it back intact")
expect(out).to_contain("LBA5 word3 survives full path")

step("A second LBA lands in a different NAND channel and round-trips independently")
expect(out).to_contain("LBA20 physical channel == 1 (DIFFERENT channel)")
expect(out).to_contain("LBA20 word3 survives full path (ch1)")

step("The end-to-end scenario reports overall PASS")
expect(out).to_contain("EMU E2E PASS")
_expect_no_fail_marker(out, "emulator end-to-end demo")
```

</details>

#### proves the memcpy seam is load-bearing and settable on both sides

- proves the memcpy seam is load-bearing and settable on both sides
- Run the emulator demo (it injects a faulting memcpy, then restores it)
   - Expected: code equals `0`
- A fault-injecting memcpy set on the DEVICE side corrupts the first data word
- Restoring the device memcpy returns the data path to clean
- A fault-injecting memcpy set on the HOST side equally corrupts the path


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proves the memcpy seam is load-bearing and settable on both sides")
step("Run the emulator demo (it injects a faulting memcpy, then restores it)")
val (out, err, code) = _run(EMU + "/nvme_emu_main.spl")
expect(code).to_equal(0)

step("A fault-injecting memcpy set on the DEVICE side corrupts the first data word")
expect(out).to_contain("device memcpy CORRUPTED word0")

step("Restoring the device memcpy returns the data path to clean")
expect(out).to_contain("clean device DMA word0")

step("A fault-injecting memcpy set on the HOST side equally corrupts the path")
expect(out).to_contain("host memcpy CORRUPTED word0")
_expect_no_fail_marker(out, "emulator memcpy seam demo")
```

</details>

### NVMe emulator: Lean4 formal and resource verification

#### verifies the NAND address codec is a bijection onto the valid page range

- verifies the NAND address codec is a bijection onto the valid page range
- Check proofs/Addr.lean with the Lean toolchain
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies the NAND address codec is a bijection onto the valid page range")
step("Check proofs/Addr.lean with the Lean toolchain")
val (out, err, code) = _lean(EMU + "/proofs/Addr.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Addr.lean")
```

</details>

#### verifies memcpy length safety (no transfer overruns the shared region)

- verifies memcpy length safety (no transfer overruns the shared region)
- Check proofs/Memcpy.lean with the Lean toolchain
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies memcpy length safety (no transfer overruns the shared region)")
step("Check proofs/Memcpy.lean with the Lean toolchain")
val (out, err, code) = _lean(EMU + "/proofs/Memcpy.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Memcpy.lean")
```

</details>

#### verifies the queue head-cursor never reads out of bounds

- verifies the queue head-cursor never reads out of bounds
- Check proofs/Queue.lean with the Lean toolchain
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies the queue head-cursor never reads out of bounds")
step("Check proofs/Queue.lean with the Lean toolchain")
val (out, err, code) = _lean(EMU + "/proofs/Queue.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Queue.lean")
```

</details>

#### verifies resource safety: the FTL allocator never reuses a page, and PRP regions are disjoint

- verifies resource safety: the FTL allocator never reuses a page, and PRP regions are disjoint
- Check proofs/Resource.lean with the Lean toolchain
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies resource safety: the FTL allocator never reuses a page, and PRP regions are disjoint")
step("Check proofs/Resource.lean with the Lean toolchain")
val (out, err, code) = _lean(EMU + "/proofs/Resource.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Resource.lean")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/hardware/nvme_fw_emulated_nand_plan.md`
- **Research:** `doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b1243611d574fa6ed5f333c3952a90b1f0e0f71a3275f1b311dc6efbba0c7d79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1243611d574fa6ed5f333c3952a90b1f0e0f71a3275f1b311dc6efbba0c7d79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1243611d574fa6ed5f333c3952a90b1f0e0f71a3275f1b311dc6efbba0c7d79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/nvme_firmware/nvme_emulator_seam_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/nvme_emulator_seam_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/nvme_firmware/nvme_emulator_seam_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/nvme_emulator_seam_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/nvme_firmware/nvme_emulator_seam_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/nvme_firmware/nvme_emulator_seam_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips the full host-to-device-to-host path on both NAND channels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/nvme_emulator_seam_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'proves the memcpy seam is load-bearing and settable on both sides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/nvme_emulator_seam_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies the NAND address codec is a bijection onto the valid page range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
