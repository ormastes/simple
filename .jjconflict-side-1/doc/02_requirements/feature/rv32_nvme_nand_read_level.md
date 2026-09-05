# RV32 NVMe NAND Read-Level Requirements

**Status:** selected by user on 2026-07-28

- **REQ-RV32-NAND-001:** Reserve non-overlapping RV32 RAM for NAND state, data,
  stored threshold level, selected read reference, read count, refresh count,
  recovery count, status, and lifecycle stage.
- **REQ-RV32-NAND-002:** Device startup must precede admin queue creation; admin
  queue creation must precede user/I/O queue creation; media operations fail
  closed before the I/O queue is ready.
- **REQ-RV32-NAND-003:** Erase, program, and read must execute against the RAM
  model. Program-over-program is rejected until erase and every erase/program
  result is checked.
- **REQ-RV32-NAND-004:** Changing the read reference must change the read result
  for injected retention and read-disturb shifts. The controller must try fixed
  downward and upward ladders without selecting from the hidden stored level,
  and stop only when ECC reports the result correctable or the ladder exhausts.
- **REQ-RV32-NAND-005:** Refresh requires both an ECC-correctable result and a
  corrected payload matching the protected data. FCR must erase, reprogram,
  read-verify, and record recovery; failed verification retires and remaps the
  page. Block-wide read counts must trigger neighbor refresh before data loss.
- **REQ-RV32-NAND-006:** QEMU/GHDL/FPGA firmware emits retained markers for
  startup, admin queue, I/O queue, erase, program, read, prevention, recovery,
  live state counters, and final pass. FPGA evidence is read through the existing
  JTAG transcript and tied to ELF/bitstream hashes.
- **REQ-RV32-NAND-007:** Admin and I/O queues have explicit absent/live/deleting
  state, bounded SQ/CQ indices, full/empty rejection, and completion telemetry.
