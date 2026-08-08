# RV32 NVMe Host AXI/MMIO System-Test Plan

## Evidence levels

- **H1 semantic:** source and scalar contract checks; useful for ABI review,
  but not transport acceptance.
- **H1 firmware parity:** QEMU runs the real RV32 ELF with an external GDB host
  driving the mailbox and guest PRP buffers. It requires command, payload, and
  NAND counters but cannot claim AXI/DMA/IRQ.
- **H1 transport:** synthesizable GHDL AXI requires real MMIO, queue DMA, IRQ,
  CQE, and NAND markers.
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

The executable SSpec invokes the aggregate GHDL runner and QEMU parity runner.
GHDL retains the focused
mocked-mailbox endpoint check and additionally boots the resident RV32 service
ELF against shared AXI RAM. Host-issued Create CQ/SQ, Identify, Write, Flush,
and Read prove SQE/CQE and payload DMA, IRQ/ack, recovery FCR, prevention refresh,
and alternate remap. QEMU repeats the firmware command/recovery sequence through
guest RAM without transport claims. Vivado/board execution and H2 remain open.

## Required artifacts for transport closure

The firmware-closure runner must retain the host trace, GHDL transcript, profile identity,
runtime identity, and binary hashes. The acceptance command must fail on
missing tools, missing traces, missing markers, nonzero subprocess status,
timeouts, or any `FAIL` marker.
