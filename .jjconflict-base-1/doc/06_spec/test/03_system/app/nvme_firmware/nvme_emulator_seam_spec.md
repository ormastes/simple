# nvme_emulator_seam_spec

> NVMe host/device emulator — end-to-end system scenario + Lean4 verification.

<!-- sdn-diagram:id=nvme_emulator_seam_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_emulator_seam_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_emulator_seam_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_emulator_seam_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-07 |
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

- Run the emulator end-to-end demo through the CLI
   - Expected: code equals `0`
- Host writes LBA 5, the device stores it in NAND, the host reads it back intact
- A second LBA lands in a different NAND channel and round-trips independently
- The end-to-end scenario reports overall PASS
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Run the emulator demo (it injects a faulting memcpy, then restores it)
   - Expected: code equals `0`
- A fault-injecting memcpy set on the DEVICE side corrupts the first data word
- Restoring the device memcpy returns the data path to clean
- A fault-injecting memcpy set on the HOST side equally corrupts the path
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Check proofs/Addr.lean with the Lean toolchain
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Addr.lean with the Lean toolchain")
val (out, err, code) = _lean(EMU + "/proofs/Addr.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Addr.lean")
```

</details>

#### verifies memcpy length safety (no transfer overruns the shared region)

- Check proofs/Memcpy.lean with the Lean toolchain
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Memcpy.lean with the Lean toolchain")
val (out, err, code) = _lean(EMU + "/proofs/Memcpy.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Memcpy.lean")
```

</details>

#### verifies the queue head-cursor never reads out of bounds

- Check proofs/Queue.lean with the Lean toolchain
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check proofs/Queue.lean with the Lean toolchain")
val (out, err, code) = _lean(EMU + "/proofs/Queue.lean")
expect(code).to_equal(0)
expect(out).to_contain("LEAN_OK")
_expect_no_fail_marker(out, "Queue.lean")
```

</details>

#### verifies resource safety: the FTL allocator never reuses a page, and PRP regions are disjoint

- Check proofs/Resource.lean with the Lean toolchain
   - Expected: code equals `0`
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Plan:** [doc/03_plan/hardware/nvme_fw_emulated_nand_plan.md](doc/03_plan/hardware/nvme_fw_emulated_nand_plan.md)
- **Research:** [doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md](doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md)


</details>
