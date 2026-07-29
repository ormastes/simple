# RV32 NVMe Host AXI/MMIO Requirements

The requirements are selected. This feature is the H1 host-transport contract
for the RV32 firmware and RAM-NAND backend. It is not PCIe or OpenSSD silicon
acceptance.

- **REQ-001 - NVMe register aperture.** An external AXI host shall read/write
  `CAP`, `VS`, `INTMS`, `INTMC`, `CC`, `CSTS`, `AQA`, `ASQ`, and `ACQ` at the
  declared NVMe offsets. Reserved writes shall not alter unrelated state.
- **REQ-002 - Reset and enable.** `CC.EN=0` shall leave `CSTS.RDY=0`. The host
  shall configure aligned admin queues before setting NVM CSS, `IOSQES=6`, and
  `IOCQES=4`; the endpoint shall set `CSTS.RDY=1` only after validation and
  shall set `CSTS.CFS=1` on unrecoverable controller failure.
- **REQ-003 - Queue and doorbell contract.** The endpoint shall support admin
  qid 0 and I/O qid 1 with depths 2..16 inclusive. Doorbells shall use
  `4 << CAP.DSTRD`, with SQ tail at `2*qid` and CQ head at `2*qid+1`.
- **REQ-004 - Host-owned queue DMA.** Host-written 64-byte SQEs shall be read
  from host queue memory and host-consumable 16-byte CQEs shall be written to
  host queue memory. The completion shall preserve CID, SQHD, SQID, phase, and
  status; internal selftest calls cannot generate acceptance evidence.
- **REQ-005 - Command floor.** The host path shall complete Identify, Create
  CQ, Create SQ, Read, Write, and Flush. A successful Read-after-Write shall
  return the exact host buffer contents through the declared PRP/DMA path.
- **REQ-006 - PRP and command validation.** The first implementation shall
  accept a dword-aligned PRP1 contained in one 4 KiB page and reject unsupported PRP2/multi-page
  transfers. Invalid PRP addresses, queue IDs/order, NSIDs, reserved fields,
  lengths, and command parameters shall complete with an error and shall not
  partially mutate media.
- **REQ-007 - NAND policy integration.** Successful host Read/Write/Flush work
  shall reach the existing RAM-NAND erase/program/read path and retain
  prevention, bounded retry, SECDED/FCR, and alternate-slot recovery behavior.
  These are backend effects, not new NVMe opcodes.
- **REQ-008 - Observable transport evidence.** The H1 test shall show MMIO
  register activity, queue-memory reads/writes, DMA data movement, interrupt
  assertion/acknowledgement, command completion consumption, and recovery
  markers. Static source checks alone do not close this requirement.
- **REQ-009 - Profile parity and fail-closed selection.** QEMU/RAM-NAND and the
  synthesizable AXI target shall run the same host-driven contract. Unknown or
  unavailable target profiles shall fail closed and shall never fall back to
  `TARGET_SIMPLE_SIM`.
- **REQ-010 - Evidence boundary.** Passing H1 evidence shall be labeled
  software/FPGA-model evidence. It shall not claim PCIe enumeration, BAR/MSI/
  PERST behavior, physical NAND, OpenSSD silicon, or KV260 board acceptance;
  those remain H2 gates.

## Traceability

| Requirement | Planned evidence |
|---|---|
| REQ-001..003 | Host AXI-Lite MMIO testbench and register/doorbell trace |
| REQ-004..006 | Host queue DMA testbench, CQE checker, negative-command cases |
| REQ-007 | Host Read/Write/Flush plus RAM-NAND recovery transcript |
| REQ-008 | MMIO, DMA, IRQ counters and retained protocol artifact |
| REQ-009 | Same SSpec against QEMU and synthesizable AXI profiles |
| REQ-010 | Profile manifest and claim-boundary checks in SSpec/manual |
