# RV32 NVMe Host AXI/MMIO System-Test Plan

## Evidence levels

- **H1 semantic:** source and scalar contract checks; useful for ABI review,
  but not transport acceptance.
- **H1 transport:** host-driven QEMU/RAM-NAND and synthesizable GHDL AXI
  runs. Requires real MMIO, queue DMA, IRQ, CQE, and NAND markers.
- **H1 FPGA-model:** KV260 only after the H1 transport gate passes and the
  host protocol is captured through the board path.
- **H2:** PCIe/OpenSSD silicon, BAR/MSI/PERST, physical NAND and vendor board
  acceptance. Not satisfied by this feature's SSpec.

## Scenarios

| ID | Requirements | Evidence |
|---|---|---|
| ST-001 | REQ-001..003 | Host writes CC/AQA/ASQ/ACQ, reads CAP/VS/CSTS, drives DSTRD-derived doorbells |
| ST-002 | REQ-004 | Host memory SQE fetch, DMA CQE write, CID/status/phase and wraparound |
| ST-003 | REQ-005 | Identify, Create CQ/SQ, Write, Read-after-Write, Flush |
| ST-004 | REQ-006 | Invalid PRP, NSID, qid/order, reserved fields and unsupported commands fail closed |
| ST-005 | REQ-007 | Host commands produce erase/program/read and prevention/retry/FCR/remap markers |
| ST-006 | REQ-008 | MMIO/DMA/IRQ counters and retained protocol transcript are nonzero and consistent |
| ST-007 | REQ-009..010 | Same H1 sequence across QEMU/GHDL; unknown profile and H2 claims rejected |

The executable SSpec now invokes the GHDL H1 endpoint runner. That runner proves
host MMIO, two posted SQE fetches, mocked firmware mailbox completion, CQE DMA,
IRQ/ack, and invalid-CC behavior. Firmware-in-the-loop payload/recovery, QEMU
parity, generator/top-level integration, and H2 remain open.

## Required artifacts for transport closure

The firmware-closure runner must retain the host trace, GHDL transcript, profile identity,
runtime identity, and binary hashes. The acceptance command must fail on
missing tools, missing traces, missing markers, nonzero subprocess status,
timeouts, or any `FAIL` marker.
