# RV32 NVMe Host AXI/MMIO NFRs

- **NFR-001 - ABI fidelity.** Register offsets, widths, queue entry sizes,
  `CAP.DSTRD`, CC fields, and CQE status encoding shall match the NVMe base
  contract represented by the driver constants.
- **NFR-002 - Bounded execution.** MMIO, DMA, queue service, and IRQ handling
  shall have bounded outstanding work and timeouts. A stalled host transaction
  shall not deadlock firmware or silently report completion.
- **NFR-003 - No allocation.** The RV32 service path shall remain usable by the
  no-alloc bare-metal build. Queue state is scalar/fixed-capacity; host memory
  is accessed through validated DMA addresses.
- **NFR-004 - Data integrity.** A command is visible to the host only after the
  CQE and payload writes are complete. Invalid PRP or queue inputs cannot cause
  out-of-range DMA or partial NAND mutation.
- **NFR-005 - Reproducibility.** QEMU and GHDL use deterministic queue addresses,
  payloads, fault injection, and trace formats. Every retained artifact records
  profile, command sequence, tool/runtime identity, and SHA-256 where binary.
- **NFR-006 - Generator provenance.** Generated VHDL and generator sources must
  agree. The endpoint cannot exist only in an ad hoc golden RTL file.
- **NFR-007 - Fail-closed evidence.** Missing runtime, compiler, simulator,
  target profile, DMA/IRQ trace, or required marker is a failed or postponed
  environment result, never a PASS.
- **NFR-008 - Claim discipline.** H1 results must state their exact transport
  and target. PCIe/OpenSSD/KV260 H2 claims require their own physical or
  vendor-specific gates.
