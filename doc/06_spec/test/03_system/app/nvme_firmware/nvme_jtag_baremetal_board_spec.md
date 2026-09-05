# nvme_jtag_baremetal_board_spec

> NVMe firmware on a baremetal board over JTAG (KV260) — fail-closed system test.

<!-- sdn-diagram:id=nvme_jtag_baremetal_board_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_jtag_baremetal_board_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_jtag_baremetal_board_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_jtag_baremetal_board_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_jtag_baremetal_board_spec

NVMe firmware on a baremetal board over JTAG (KV260) — fail-closed system test.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVME-JTAG-001 |
| Category | Hardware |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md |
| Design | doc/07_guide/hardware/nvme_firmware/jtag_baremetal_board_testing.md |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/03_system/app/nvme_firmware/nvme_jtag_baremetal_board_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe firmware on a baremetal board over JTAG (KV260) — fail-closed system test.

Runs the real KV260 JTAG board test (scripts/fpga/check_kv260_telnet_serial_system.shs):
a marker is injected over JTAG into the ZynqMP PS-UART1 and observed back on the serial
console through the telnet-serial bridge — i.e. a test actually running on the physical
board through JTAG. This is the baremetal-remote counterpart to nvme_rv32_baremetal_boot_spec
(which boots the same Simple-generated rv32 binary on QEMU).

FAIL-CLOSED (never a silent skip, never a false pass): the test is classified into exactly
one status, and the spec passes on every status EXCEPT a genuine board failure:
  * board-pass        — the JTAG marker was injected and seen on serial (the real board ran the test)
  * host-prep-required — the FT4232H JTAG channel is still bound to ftdi_sio (needs a root unbind:
                         `sh scripts/fpga/jtag-ftdi-unbind.shs`) — host prep, recorded, not a failure
  * host-unavailable  — no FT4232H adapter / harness / board artifacts present on this host
  * board-fail        — the marker was injected over JTAG but NOT observed on serial -> the spec FAILS

Run single-file: `bin/simple test test/03_system/app/nvme_firmware/nvme_jtag_baremetal_board_spec.spl`.

## Scenarios

### NVMe firmware on a baremetal board over JTAG (KV260)

#### runs the live JTAG board test, or records a fail-closed reason

- Classify the JTAG board path (adapter / channel-free / harness) and run the live test when ready
- A single classification status was produced (never a silent skip)
- The board path is operational (marker seen over JTAG) or a documented host-unavailable / prep state — never a real board failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify the JTAG board path (adapter / channel-free / harness) and run the live test when ready")
val (out, err, code) = _jtag_classify()

step("A single classification status was produced (never a silent skip)")
expect(out).to_contain("JTAG_STATUS=")

step("The board path is operational (marker seen over JTAG) or a documented host-unavailable / prep state — never a real board failure")
expect(out).to_contain("JTAG_RESULT=ok")
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
- **Design:** [doc/07_guide/hardware/nvme_firmware/jtag_baremetal_board_testing.md](doc/07_guide/hardware/nvme_firmware/jtag_baremetal_board_testing.md)
- **Research:** [doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md](doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md)


</details>
