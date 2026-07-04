# nvme_integration_spec

> NVMe firmware + emulator end-to-end integration scenarios.

<!-- sdn-diagram:id=nvme_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

- Run the firmware end-to-end simulation through the CLI
   - Expected: code equals `0`
- The joined HIL/FTL/FIL scenario reports overall end-to-end PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the firmware end-to-end simulation through the CLI")
val (out, err, code) = _run(FW + "/sim_main.spl")
expect(code).to_equal(0)

step("The joined HIL/FTL/FIL scenario reports overall end-to-end PASS")
expect(out).to_contain("ALL END-TO-END CHECKS PASS")
```

</details>

### NVMe firmware NVMe controller admin+IO-queue integration

#### processes admin and multi IO-queue traffic end-to-end through the controller

- Run the NVMe controller end-to-end scenario through the CLI
   - Expected: code equals `0`
- The controller admin + IO-queue scenario reports overall end-to-end PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the NVMe controller end-to-end scenario through the CLI")
val (out, err, code) = _run(FW + "/nvme_main.spl")
expect(code).to_equal(0)

step("The controller admin + IO-queue scenario reports overall end-to-end PASS")
expect(out).to_contain("ALL NVME CONTROLLER E2E CHECKS PASS")
```

</details>

### NVMe host/device emulator integration

#### joins the host and device emulator over the memcpy/DMA seam end-to-end

- Run the host/device emulator end-to-end demo through the CLI
   - Expected: code equals `0`
- The joined host/device emulator scenario reports overall end-to-end PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Plan:** [doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md](doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md)
- **Research:** [doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md](doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md)


</details>
