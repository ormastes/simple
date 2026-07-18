# nvme_units_spec

> NVMe firmware + emulator unit self-tests (per-layer leaf coverage).

<!-- sdn-diagram:id=nvme_units_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_units_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_units_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_units_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_units_spec

NVMe firmware + emulator unit self-tests (per-layer leaf coverage).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVME-UNIT-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md |
| Design | N/A |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/01_unit/app/nvme_firmware/nvme_units_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe firmware + emulator unit self-tests (per-layer leaf coverage).

The unit tier exercises the pure-Simple firmware and emulator self-test
aggregators that live under examples/09_embedded/simpleos_nvme_fw/. Those modules
cannot be bare-imported from test/ (cross-example import is unsupported), so the
tier drives each aggregator through the real CLI (`bin/simple run`) as a
subprocess and asserts the operator-visible per-layer PASS evidence — exactly
what the generated manual shows. Run:
`bin/simple test test/01_unit/app/nvme_firmware/nvme_units_spec.spl`.

## Scenarios

### NVMe firmware unit self-tests (per-layer)

#### passes every per-layer firmware self-test (FIL, FTL, HIL, NVMe controller)

- Run the firmware self-test aggregator through the CLI
   - Expected: code equals `0`
- The FIL (flash interface) layer reports its self-test section
- The FTL (translation) layer reports its self-test section
- The HIL (host interface) layer reports its self-test section
- The NVMe controller (admin + multi IO queue) reports its self-test section
- The aggregator reports overall firmware PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the firmware self-test aggregator through the CLI")
val (out, err, code) = _run(FW + "/test_fw.spl")
expect(code).to_equal(0)

step("The FIL (flash interface) layer reports its self-test section")
expect(out).to_contain("FIL (flash interface)")

step("The FTL (translation) layer reports its self-test section")
expect(out).to_contain("FTL (translation)")

step("The HIL (host interface) layer reports its self-test section")
expect(out).to_contain("HIL (host interface)")

step("The NVMe controller (admin + multi IO queue) reports its self-test section")
expect(out).to_contain("NVMe controller (admin + multi IO queue)")

step("The aggregator reports overall firmware PASS")
expect(out).to_contain("ALL FIRMWARE SELF-TESTS PASS")
```

</details>

### NVMe emulator unit self-tests

#### passes every emulator module self-test (NAND, memcpy, FTL, device)

- Run the emulator self-test aggregator through the CLI
   - Expected: code equals `0`
- The aggregator reports overall emulator PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the emulator self-test aggregator through the CLI")
val (out, err, code) = _run(EMU + "/test_emu.spl")
expect(code).to_equal(0)

step("The aggregator reports overall emulator PASS")
expect(out).to_contain("ALL EMU SELFTESTS PASS")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md](doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md)
- **Research:** [doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md](doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md)


</details>
