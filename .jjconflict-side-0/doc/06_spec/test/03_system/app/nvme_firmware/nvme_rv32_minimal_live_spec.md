# nvme_rv32_minimal_live_spec

> This is not the full SimpleOS boot image. It proves the bounded pure-Simple RV32 firmware hook slices build, link, boot under QEMU, and print the firmware PASS marker.

<!-- sdn-diagram:id=nvme_rv32_minimal_live_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_rv32_minimal_live_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_rv32_minimal_live_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_rv32_minimal_live_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_rv32_minimal_live_spec

This is not the full SimpleOS boot image. It proves the bounded pure-Simple RV32 firmware hook slices build, link, boot under QEMU, and print the firmware PASS marker.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVME-RV32-MINIMAL-LIVE-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md |
| Design | N/A |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/03_system/app/nvme_firmware/nvme_rv32_minimal_live_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This is not the full SimpleOS boot image. It proves the bounded pure-Simple
RV32 firmware hook slices build, link, boot under QEMU, and print the firmware
PASS marker.

The checker uses `scripts/check/check-nvme-rv32-minimal-live.shs` with
`NVME_RV32_MINIMAL_SECTIONS=21`, which covers every registered firmware slice in
the bounded minimal live surface: RAIN, ECC, journal, map, band, scheduler,
power/thermal, HIL, queue phase, IO command, flush, admin, reactor, policy
target, DRAM durability, wear scrub, media retire, power cycle, backpressure
abort, feature guard, and namespace guard.

## Syntax

Run the executable system spec:

```sh
bin/simple test test/03_system/app/nvme_firmware/nvme_rv32_minimal_live_spec.spl --mode=interpreter --clean --timeout 180 --sequential
```

Run the underlying fail-closed checker directly:

```sh
NVME_RV32_MINIMAL_SECTIONS=21 NVME_RV32_BUILD_TIMEOUT_SECS=120 RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs
```

## Expected Evidence

The checker must compile the generated RV32 firmware object, link it with the
tiny RV32 start stub, boot the ELF under `qemu-system-riscv32`, and print both
`ALL RV32 NVME FW CHECKS PASS` and `STATUS: PASS nvme-rv32-minimal-live`.

## Scenarios

### NVMe firmware RV32 minimal live gate

#### builds and boots all registered minimal RV32 firmware slices

- Run the 21-section RV32 minimal live checker
   - Expected: code equals `0`
- The checker reports the RV32 firmware serial PASS marker
- The checker output contains no failure marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the 21-section RV32 minimal live checker")
val cmd = "NVME_RV32_MINIMAL_SECTIONS=21 NVME_RV32_BUILD_TIMEOUT_SECS=120 RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs"
val (out, err, code) = _run(cmd)
expect(code).to_equal(0)

step("The checker reports the RV32 firmware serial PASS marker")
expect(out).to_contain("ALL RV32 NVME FW CHECKS PASS")
expect(out).to_contain("STATUS: PASS nvme-rv32-minimal-live")

step("The checker output contains no failure marker")
if out.contains("FAIL"):
    fail("SERIAL-FAIL: minimal live checker printed a failure marker")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md](doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md)
- **Research:** [doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md](doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md)


</details>
